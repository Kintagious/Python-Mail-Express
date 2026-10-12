#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Express Mail - a modern-day e-mail client for Windows 11 that looks and feels
like Outlook Express 6 on Windows XP.

  * Real mail: IMAP (receive) + SMTP (send) over SSL/TLS, multiple accounts
  * The classic layout: Folders + Contacts panes, message list, preview pane,
    the big blue folder band, the start page and the Send/Recv progress window
  * Local Folders (Inbox, Outbox, Sent Items, Deleted Items, Drafts) + your own
  * Address Book, drafts, attachments, priority, flags, printing,
    .eml import / export, auto-check every N minutes, tray notification
  * XP "Luna" styling: Tahoma 8pt, beige toolbars, blue scrollbars,
    #316AC5 selection, and a blue Windows 11 title bar (via DWM)

Requires Python 3.10+ and:  pip install PySide6 keyring
Your mail lives in %APPDATA%\\ExpressMail  (mail.db + config.json).
Passwords are kept in Windows Credential Manager when `keyring` is installed.
"""

import base64
import html
import imaplib
import math
import mimetypes
import os
import random
import re
import smtplib
import sqlite3
import ssl
import sys
import time
import uuid
import json
import shutil
import hashlib
import secrets
import threading
import urllib.error
import urllib.parse
import urllib.request
import webbrowser
from http.server import BaseHTTPRequestHandler, HTTPServer
from datetime import datetime
from email import policy
from email.message import EmailMessage
from email.parser import BytesParser
from email.utils import (formataddr, formatdate, getaddresses, make_msgid,
                         parsedate_to_datetime)
from pathlib import Path

from PySide6.QtCore import (QByteArray, QEvent, QObject, QPoint, QPointF, QRect,
                            QRectF, QSize, Qt, QThread, QTimer, QUrl, Signal)
from PySide6.QtGui import (QAction, QBrush, QColor, QDesktopServices, QFont,
                           QFontMetrics, QIcon, QKeySequence, QLinearGradient,
                           QPainter, QPainterPath, QPalette, QPen, QPixmap,
                           QPolygonF, QTextCharFormat, QTextCursor, QTextDocument,
                           QShortcut, QTextListFormat)
from PySide6.QtWidgets import (
    QApplication, QCheckBox, QColorDialog, QComboBox, QCompleter, QDialog,
    QDialogButtonBox, QFileDialog, QFontComboBox, QFormLayout, QFrame,
    QGridLayout, QGroupBox, QHBoxLayout, QHeaderView, QInputDialog, QLabel,
    QLineEdit, QListView, QListWidget, QListWidgetItem, QMainWindow, QMenu, QMessageBox,
    QProgressBar, QPushButton, QSpinBox, QSplitter, QStackedWidget, QStyle,
    QStyledItemDelegate, QStyleFactory, QStyleOptionViewItem,
    QSystemTrayIcon, QTabWidget, QTableWidget, QTableWidgetItem, QTextBrowser,
    QTextEdit, QToolBar, QToolButton, QTreeWidget, QTreeWidgetItem,
    QVBoxLayout, QWidget, QAbstractItemView, QAbstractButton, QButtonGroup, QRadioButton)

try:
    from PySide6.QtPrintSupport import QPrintDialog, QPrinter
except Exception:  # printing support is optional
    QPrinter = QPrintDialog = None

try:
    import keyring
except Exception:
    keyring = None

try:  # Chromium-based viewer for HTML mail (part of the normal PySide6 install)
    from PySide6.QtWebEngineCore import (QWebEnginePage, QWebEngineProfile, QWebEngineSettings,
                                         QWebEngineUrlRequestInterceptor)
    from PySide6.QtWebEngineWidgets import QWebEngineView
    HAVE_WEBENGINE = True
except Exception:
    HAVE_WEBENGINE = False

if HAVE_WEBENGINE:
    class RemoteBlocker(QWebEngineUrlRequestInterceptor):
        """Blocks everything from the internet (pictures, tracking pixels, fonts) unless allowed."""

        def __init__(self, parent=None):
            super().__init__(parent)
            self.allow = False

        def interceptRequest(self, info):
            if not self.allow and info.requestUrl().scheme().lower() in ("http", "https", "ftp", "ws", "wss"):
                info.block(True)

    class MailPage(QWebEnginePage):
        """Links open in your normal browser; mailto: links open a new message."""

        def __init__(self, profile, parent, main):
            super().__init__(profile, parent)
            self.main = main

        def _open(self, url):
            if url.scheme() == "mailto":
                self.main.compose(to=url.path())
            elif url.scheme() in ("http", "https"):
                QDesktopServices.openUrl(url)

        def acceptNavigationRequest(self, url, nav_type, is_main_frame):
            if nav_type == QWebEnginePage.NavigationTypeLinkClicked:
                self._open(url)
                return False
            return True

        def createWindow(self, _type):          # links with target=_blank
            tmp = QWebEnginePage(self.profile(), self)
            tmp.urlChanged.connect(lambda u: (self._open(u), tmp.deleteLater()))
            return tmp

APP_NAME = "Python Mail Express"
VERSION = "1.0"
APP_DIR = Path(os.environ.get("APPDATA") or (Path.home() / ".config")) / "ExpressMail"
APP_DIR.mkdir(parents=True, exist_ok=True)

SPECIAL_FOLDERS = ["Inbox", "Outbox", "Sent Items", "Deleted Items", "Drafts"]
FOLDER_ICONS = {"Inbox": "inbox", "Outbox": "outbox", "Sent Items": "sent",
                "Deleted Items": "deleted", "Drafts": "drafts"}
OUTGOING_FOLDERS = {"Outbox", "Sent Items", "Drafts"}
BLOCKED_EXT = {".exe", ".bat", ".cmd", ".com", ".scr", ".pif", ".vbs", ".vbe",
               ".js", ".jse", ".wsf", ".wsh", ".ps1", ".msi", ".msp", ".lnk",
               ".hta", ".cpl", ".reg", ".jar"}

ID_ROLE = Qt.UserRole
SORT_ROLE = Qt.UserRole + 2
COUNT_ROLE = Qt.UserRole + 1

TIPS = [
    "Press Ctrl+M at any time to send and receive all of your mail.",
    "Ctrl+F forwards the selected message, just like it always did.",
    "Drafts are saved automatically when you close a message and choose Yes.",
    "Right-click a folder to create, rename or delete your own folders.",
    "Gmail, Yahoo and iCloud need an app password, not your normal password.",
    "Messages you delete go to Deleted Items. Empty it from the Edit menu.",
    "Double-click a contact to start a new message to them.",
    "Set how often new mail is checked in Tools > Options.",
]

# --------------------------------------------------------------------------
# Icons (drawn in code on a 32x32 grid - no image files needed)
# --------------------------------------------------------------------------


def _grad(x0, y0, x1, y1, c0, c1):
    g = QLinearGradient(x0, y0, x1, y1)
    g.setColorAt(0, QColor(c0))
    g.setColorAt(1, QColor(c1))
    return QBrush(g)


def _shape(p, pts, fill, border=None, width=1.0):
    p.setPen(QPen(QColor(border), width) if border else Qt.NoPen)
    p.setBrush(fill if isinstance(fill, QBrush) else QBrush(QColor(fill)))
    p.drawPolygon(QPolygonF([QPointF(x, y) for x, y in pts]))


def _pen(color, w, round_cap=True):
    pen = QPen(QColor(color), w)
    if round_cap:
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
    return pen


def _env(p, x, y, w, h, opened=False):
    if opened:
        _shape(p, [(x, y), (x + w / 2, y - h * 0.6), (x + w, y)],
               _grad(0, y - h * 0.6, 0, y, "#F6EECF", "#E0D09A"), "#806A32", 1.1)
    p.setPen(QPen(QColor("#806A32"), 1.1))
    p.setBrush(_grad(x, y, x, y + h, "#FFFFFF", "#EDE3BF"))
    p.drawRect(QRectF(x, y, w, h))
    p.setPen(QPen(QColor("#A08A4E"), 1.0))
    mid = y + h * (0.5 if opened else 0.58)
    p.drawLine(QPointF(x, y), QPointF(x + w / 2, mid))
    p.drawLine(QPointF(x + w / 2, mid), QPointF(x + w, y))


def _harrow(p, x0, x1, y, color, t=5.0):
    d = 1 if x1 > x0 else -1
    hl = t * 1.5
    pts = [(x0, y - t / 2), (x1 - d * hl, y - t / 2), (x1 - d * hl, y - t * 1.3),
           (x1, y), (x1 - d * hl, y + t * 1.3), (x1 - d * hl, y + t / 2), (x0, y + t / 2)]
    _shape(p, pts, color, QColor(color).darker(150).name(), 0.9)


def _varrow(p, x, y0, y1, color, t=5.0):
    d = 1 if y1 > y0 else -1
    hl = t * 1.5
    pts = [(x - t / 2, y0), (x - t / 2, y1 - d * hl), (x - t * 1.3, y1 - d * hl),
           (x, y1), (x + t * 1.3, y1 - d * hl), (x + t / 2, y1 - d * hl), (x + t / 2, y0)]
    _shape(p, pts, color, QColor(color).darker(150).name(), 0.9)


def _star(p, cx, cy, r):
    pts = []
    for i in range(10):
        ang = math.pi / 2 + i * math.pi / 5
        rr = r if i % 2 == 0 else r * 0.45
        pts.append((cx + rr * math.cos(ang), cy - rr * math.sin(ang)))
    _shape(p, pts, "#FFD21F", "#B8860B", 0.9)


def _folder(p):
    _shape(p, [(3, 8), (11, 8), (13, 10.5), (28, 10.5), (28, 26), (3, 26)],
           _grad(0, 8, 0, 26, "#F5CF62", "#D9A02A"), "#A87A16")
    _shape(p, [(6, 14), (30.5, 14), (28, 27), (3, 27)],
           _grad(0, 14, 0, 27, "#FFF2B8", "#F2C447"), "#A87A16")


def _tray(p):
    _shape(p, [(2, 17), (30, 17), (30, 29), (2, 29)],
           _grad(0, 17, 0, 29, "#E2EAF8", "#8EA8D6"), "#46608F")
    _shape(p, [(7, 17), (25, 17), (23, 22), (9, 22)], "#F7F9FF", "#46608F")


def _i_new(p):
    _env(p, 2, 11, 24, 17)
    _star(p, 24.5, 8, 7.5)


def _i_reply(p):
    _env(p, 10, 13, 20, 15)
    _harrow(p, 24, 2, 9, "#8E44C9")


def _i_replyall(p):
    _env(p, 11, 15, 19, 14)
    _harrow(p, 26, 8, 6, "#8E44C9", 4)
    _harrow(p, 22, 2, 12, "#8E44C9", 4)


def _i_forward(p):
    _env(p, 2, 13, 20, 15)
    _harrow(p, 8, 30, 9, "#2C6BD8")


def _i_print(p):
    _shape(p, [(9, 3), (23, 3), (23, 14), (9, 14)], "#FFFFFF", "#7A7A7A")
    p.setPen(QPen(QColor("#9DB4DB"), 1))
    for yy in (6.5, 9.5):
        p.drawLine(QPointF(11, yy), QPointF(21, yy))
    p.setPen(QPen(QColor("#555555"), 1))
    p.setBrush(_grad(0, 12, 0, 25, "#EDEDED", "#9C9C9C"))
    p.drawRoundedRect(QRectF(3, 12, 26, 12), 2, 2)
    _shape(p, [(8, 20), (24, 20), (24, 29), (8, 29)], "#FFFFFF", "#7A7A7A")
    p.setPen(Qt.NoPen)
    p.setBrush(QColor("#2ECC40"))
    p.drawEllipse(QRectF(24, 15, 3, 3))


def _i_delete(p):
    for col, w in (("#7A0E0E", 7.5), ("#E8402F", 4.5)):
        p.setPen(_pen(col, w))
        p.drawLine(QPointF(7, 7), QPointF(25, 25))
        p.drawLine(QPointF(25, 7), QPointF(7, 25))


def _i_sendrecv(p):
    _env(p, 2, 4, 17, 12)
    _env(p, 13, 16, 17, 12)
    _varrow(p, 26, 14, 2, "#2E9E3E", 4.5)
    _varrow(p, 6, 18, 30, "#2C6BD8", 4.5)


def _i_addresses(p):
    p.setPen(QPen(QColor("#1D3E86"), 1))
    p.setBrush(_grad(6, 0, 28, 0, "#4A7EE0", "#2450B0"))
    p.drawRoundedRect(QRectF(6, 3, 21, 26), 2, 2)
    p.setPen(Qt.NoPen)
    p.setBrush(QColor("#FFFFFF"))
    p.drawRect(QRectF(26, 5, 2.5, 22))
    p.setBrush(QColor("#17306B"))
    p.drawRect(QRectF(6, 3, 4, 26))
    p.setBrush(QColor("#FFFFFF"))
    p.drawEllipse(QRectF(15, 8, 7, 7))
    path = QPainterPath()
    path.moveTo(12, 24)
    path.cubicTo(12, 15.5, 25, 15.5, 25, 24)
    path.closeSubpath()
    p.drawPath(path)


def _i_find(p):
    p.setPen(_pen("#7B4A1E", 5))
    p.drawLine(QPointF(19.5, 19.5), QPointF(28, 28))
    p.setPen(QPen(QColor("#3A3A3A"), 2.6))
    p.setBrush(QColor(205, 228, 255, 200))
    p.drawEllipse(QPointF(13, 13), 8.5, 8.5)
    p.setPen(_pen("#FFFFFF", 1.8))
    p.drawArc(QRectF(8, 8, 10, 10), 100 * 16, 70 * 16)


def _i_folder(p):
    _folder(p)


def _i_local(p):
    _folder(p)
    p.setPen(QPen(QColor("#333333"), 1))
    p.setBrush(QColor("#D9D9D9"))
    p.drawRect(QRectF(17, 15, 13, 10))
    p.setBrush(_grad(0, 17, 0, 23, "#5E95F0", "#1E55C8"))
    p.drawRect(QRectF(19, 17, 9, 6))
    p.setBrush(QColor("#999999"))
    p.drawRect(QRectF(21, 25, 5, 3))


def _i_inbox(p):
    _env(p, 9, 3, 14, 11)
    _tray(p)


def _i_outbox(p):
    _env(p, 6, 5, 14, 11)
    _tray(p)
    _varrow(p, 26, 15, 2, "#2E9E3E", 4)


def _i_sent(p):
    _env(p, 2, 6, 22, 16)
    _harrow(p, 11, 31, 25, "#2E9E3E", 4.5)


def _i_deleted(p):
    p.setPen(QPen(QColor("#4E5B6B"), 1))
    p.setBrush(_grad(8, 0, 24, 0, "#D3DCE6", "#8C99AA"))
    p.drawPolygon(QPolygonF([QPointF(8, 9), QPointF(24, 9), QPointF(22, 29), QPointF(10, 29)]))
    p.drawRoundedRect(QRectF(6, 6, 20, 3.5), 1, 1)
    p.drawRect(QRectF(13, 3.5, 6, 2.5))
    p.setPen(QPen(QColor("#5E6B7C"), 1.2))
    for x in (12.5, 16, 19.5):
        p.drawLine(QPointF(x, 12), QPointF(x, 26))


def _i_drafts(p):
    _shape(p, [(6, 3), (19, 3), (24, 8), (24, 29), (6, 29)], "#FFFFFF", "#7A7A7A")
    _shape(p, [(19, 3), (19, 8), (24, 8)], "#E4E4E4", "#7A7A7A")
    p.setPen(QPen(QColor("#9DB4DB"), 1))
    for yy in (12, 16, 20):
        p.drawLine(QPointF(9, yy), QPointF(21, yy))
    p.setPen(_pen("#C68A12", 4.5))
    p.drawLine(QPointF(15, 26), QPointF(28, 11))
    p.setPen(_pen("#333333", 2))
    p.drawLine(QPointF(14.5, 26.5), QPointF(13, 28.5))


def _i_app(p):
    p.setPen(QPen(QColor("#163C93"), 1.2))
    p.setBrush(_grad(4, 2, 28, 30, "#8DBBFF", "#1D4FC4"))
    p.drawEllipse(QRectF(1.5, 1.5, 29, 29))
    _env(p, 7, 10, 18, 13)
    p.setPen(_pen("#4CD25A", 2.6))
    p.setBrush(Qt.NoBrush)
    p.drawArc(QRectF(4.5, 4.5, 23, 23), 200 * 16, 150 * 16)


def _i_contact(p):
    p.setPen(QPen(QColor("#1D3E86"), 1))
    path = QPainterPath()
    path.moveTo(4, 30)
    path.cubicTo(4, 16, 28, 16, 28, 30)
    path.closeSubpath()
    p.setBrush(_grad(0, 18, 0, 30, "#5C8EE6", "#2450B0"))
    p.drawPath(path)
    p.setPen(QPen(QColor("#8A5A30"), 1))
    p.setBrush(QColor("#F6C99B"))
    p.drawEllipse(QRectF(10, 3, 12, 12))


def _i_unread(p):
    _env(p, 2, 7, 28, 19)


def _i_read(p):
    _env(p, 2, 13, 28, 16, True)


def _i_attach(p):
    p.setPen(_pen("#4A4A4A", 2.4))
    p.setBrush(Qt.NoBrush)
    path = QPainterPath()
    path.moveTo(19, 10)
    path.lineTo(19, 23)
    path.arcTo(QRectF(13, 20, 6, 6), 0, -180)
    path.lineTo(13, 7)
    path.arcTo(QRectF(13, 2.5, 9, 9), 180, -180)
    path.lineTo(22, 25)
    path.arcTo(QRectF(10, 19.5, 12, 12), 0, -180)
    path.lineTo(10, 11)
    p.drawPath(path)


def _i_flag(p):
    p.setPen(_pen("#333333", 2))
    p.drawLine(QPointF(8, 3), QPointF(8, 30))
    _shape(p, [(9, 4), (27, 9.5), (9, 16)], "#E8402F", "#8A1A12")


def _i_high(p):
    f = QFont("Arial")
    f.setBold(True)
    f.setPixelSize(30)
    p.setFont(f)
    p.setPen(QColor("#D0201A"))
    p.drawText(QRectF(0, 0, 32, 32), Qt.AlignCenter, "!")


def _i_low(p):
    _varrow(p, 16, 4, 29, "#2C6BD8", 6)


def _i_send(p):
    _env(p, 9, 9, 21, 15)
    p.setPen(_pen("#2C6BD8", 2.2))
    for x0, yy in ((1, 12), (3, 17), (1, 22)):
        p.drawLine(QPointF(x0, yy), QPointF(7, yy))


def _i_save(p):
    p.setPen(QPen(QColor("#1C2E5C"), 1))
    p.setBrush(_grad(0, 3, 0, 29, "#4B6FC4", "#2A4592"))
    p.drawRoundedRect(QRectF(3, 3, 26, 26), 2, 2)
    p.setBrush(QColor("#FFFFFF"))
    p.drawRect(QRectF(8, 16, 16, 11))
    p.setBrush(_grad(10, 0, 22, 0, "#E8E8E8", "#A8A8A8"))
    p.drawRect(QRectF(10, 3, 12, 9))
    p.setBrush(QColor("#2A4592"))
    p.drawRect(QRectF(17, 4.5, 3, 6))


def _i_cut(p):
    p.setPen(_pen("#8A8A8A", 2.2))
    p.drawLine(QPointF(12.5, 21), QPointF(22, 3))
    p.drawLine(QPointF(19.5, 21), QPointF(10, 3))
    p.setPen(QPen(QColor("#B02020"), 2.4))
    p.setBrush(Qt.NoBrush)
    p.drawEllipse(QRectF(4, 20, 9, 9))
    p.drawEllipse(QRectF(19, 20, 9, 9))


def _i_copy(p):
    for x, y in ((4, 3), (12, 10)):
        _shape(p, [(x, y), (x + 13, y), (x + 16, y + 3), (x + 16, y + 19), (x, y + 19)],
               "#FFFFFF", "#6A6A6A")
        p.setPen(QPen(QColor("#9DB4DB"), 1))
        for k in range(3):
            p.drawLine(QPointF(x + 3, y + 7 + k * 4), QPointF(x + 13, y + 7 + k * 4))


def _i_paste(p):
    p.setPen(QPen(QColor("#6B4012"), 1))
    p.setBrush(_grad(0, 5, 0, 30, "#C98C45", "#9A5E22"))
    p.drawRoundedRect(QRectF(4, 5, 19, 25), 2, 2)
    p.setBrush(QColor("#BBBBBB"))
    p.drawRoundedRect(QRectF(9, 2, 9, 6), 1.5, 1.5)
    _shape(p, [(14, 12), (29, 12), (29, 30), (14, 30)], "#FFFFFF", "#6A6A6A")


def _i_undo(p):
    p.setPen(_pen("#2C6BD8", 3.5))
    p.setBrush(Qt.NoBrush)
    path = QPainterPath()
    path.moveTo(10, 12)
    path.cubicTo(25, 7, 31, 23, 17, 27)
    p.drawPath(path)
    _shape(p, [(3, 12), (12, 5.5), (12, 18.5)], "#2C6BD8", "#1A4590")


def _align(p, mode):
    p.setPen(_pen("#222222", 2.2))
    for i, y in enumerate((7, 12, 17, 22, 27)):
        w = 24 if i % 2 == 0 else 16
        x = {"l": 4, "c": 16 - w / 2, "r": 28 - w}[mode]
        p.drawLine(QPointF(x, y), QPointF(x + w, y))


def _i_bullets(p):
    for y in (8, 16, 24):
        p.setPen(Qt.NoPen)
        p.setBrush(QColor("#222222"))
        p.drawEllipse(QPointF(6, y), 2.4, 2.4)
        p.setPen(_pen("#222222", 2.2))
        p.drawLine(QPointF(12, y), QPointF(28, y))


def _i_numbers(p):
    f = QFont("Arial")
    f.setPixelSize(9)
    f.setBold(True)
    p.setFont(f)
    for i, y in enumerate((8, 16, 24)):
        p.setPen(QColor("#222222"))
        p.drawText(QRectF(1, y - 6, 9, 12), Qt.AlignCenter, str(i + 1))
        p.setPen(_pen("#222222", 2.2))
        p.drawLine(QPointF(12, y), QPointF(28, y))


def _i_color(p):
    f = QFont("Times New Roman")
    f.setPixelSize(24)
    f.setBold(True)
    p.setFont(f)
    p.setPen(QColor("#222222"))
    p.drawText(QRectF(0, -2, 32, 26), Qt.AlignCenter, "A")
    p.setPen(Qt.NoPen)
    p.setBrush(QColor("#E8402F"))
    p.drawRect(QRectF(5, 24, 22, 5))


def _arrow_glyph(p, direction):
    pts = {"up": [(16, 9), (25, 21), (7, 21)], "down": [(7, 11), (25, 11), (16, 23)],
           "left": [(9, 16), (21, 7), (21, 25)], "right": [(23, 16), (11, 7), (11, 25)]}
    _shape(p, pts[direction], THEME["arrow"])


ICON_PAINTERS = {
    "new": _i_new, "reply": _i_reply, "replyall": _i_replyall, "forward": _i_forward,
    "print": _i_print, "delete": _i_delete, "sendrecv": _i_sendrecv,
    "addresses": _i_addresses, "find": _i_find, "folder": _i_folder, "local": _i_local,
    "inbox": _i_inbox, "outbox": _i_outbox, "sent": _i_sent, "deleted": _i_deleted,
    "drafts": _i_drafts, "app": _i_app, "contact": _i_contact, "unread": _i_unread,
    "read": _i_read, "attach": _i_attach, "flag": _i_flag, "high": _i_high,
    "low": _i_low, "send": _i_send, "save": _i_save, "cut": _i_cut, "copy": _i_copy,
    "paste": _i_paste, "undo": _i_undo, "bullets": _i_bullets, "numbers": _i_numbers,
    "color": _i_color,
    "al_left": lambda p: _align(p, "l"), "al_center": lambda p: _align(p, "c"),
    "al_right": lambda p: _align(p, "r"),
    "arr_up": lambda p: _arrow_glyph(p, "up"), "arr_down": lambda p: _arrow_glyph(p, "down"),
    "arr_left": lambda p: _arrow_glyph(p, "left"), "arr_right": lambda p: _arrow_glyph(p, "right"),
}


def make_pixmap(name, size=32):
    pm = QPixmap(size, size)
    pm.fill(Qt.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    p.setRenderHint(QPainter.TextAntialiasing)
    p.scale(size / 32.0, size / 32.0)
    ICON_PAINTERS[name](p)
    p.end()
    return pm


_ICON_CACHE = {}


def icon(name):
    if name not in _ICON_CACHE:
        ic = QIcon()
        for s in (16, 20, 24, 32, 48, 64):
            ic.addPixmap(make_pixmap(name, s))
        _ICON_CACHE[name] = ic
    return _ICON_CACHE[name]


# --------------------------------------------------------------------------
# XP color schemes: Default (blue), Olive Green, Silver, Zune
# --------------------------------------------------------------------------

_CLOSE = {"close": ("#E8866A", "#C13A1D"), "close_hover": ("#F7A58E", "#D6482A"),
          "close_down": ("#B53A1E", "#E9886D")}

THEMES = {
    "Blue": dict(
        label="Default (blue)",
        face="#ECE9D8", border="#ACA899", sep="#C5C2B2", menubar_line="#D4D0C8",
        toolbar=("#FEFEFD", "#F3F1E8", "#E3DFCC"),
        sel="#316AC5", sel_text="#FFFFFF", sel_inactive="#D4D0C8",
        hover_border="#C2BFAE", hover=("#FFFFFF", "#E6E3D3"),
        down_border="#9D9A87", down=("#DEDBCB", "#EFEDE3"),
        band=("#1F4FC2", "#3F74DC", "#7EA6EE"), band_border="#12317E",
        pane=("#FFFFFF", "#E4E1D2"), preview=("#F7F6F0", "#E3E0CF"), list_border="#7F9DB9",
        header=("#FFFFFF", "#F1EFE2", "#E2DECD"), header_line="#D6D2C2", header_hover="#F9B119",
        button_border="#003C74", button_hover="#E5A01A", button_default="#3C7FB1",
        tab_accent="#FFC83C", group_title="#0046D5", group_border="#D0D0BF",
        scroll_track="#F4F3EE", scroll=("#CAD9FC", "#BCCFFA", "#ADC3F4"), scroll_border="#A1B5E8",
        scroll_hover="#D8E4FE", scroll_btn=("#DCE6FD", "#B4C9F6"), arrow="#4D6185",
        title_active=[(0, "#0997FF"), (0.08, "#0053EE"), (0.40, "#0050EE"), (0.88, "#0066FF"),
                      (0.93, "#0066FF"), (0.95, "#005BFF"), (0.96, "#003DD7"), (1, "#003DD7")],
        title_inactive=[(0, "#7697E7"), (0.03, "#7E9EE3"), (0.06, "#94AFE8"), (0.08, "#97B4E9"),
                        (0.14, "#82A5E4"), (0.17, "#7C9FE2"), (0.25, "#7996DE"), (0.56, "#7B99E1"),
                        (0.81, "#82A9E9"), (0.89, "#80A5E7"), (0.94, "#7B96E1"), (0.97, "#7A93DF"),
                        (1, "#ABBAE3")],
        title_text="#FFFFFF", title_shadow="#0F1089", title_text_inactive="#D8E4F8",
        cap=("#6F9DF7", "#1B52D8"), cap_hover=("#97BAFF", "#2F69EA"), cap_down=("#1A45B8", "#5F8FF0"),
        cap_border="#FFFFFF", cap_glyph="#FFFFFF",
        edge_lt=["#0831D9", "#166AEE", "#0855DD", "#0855DD"],
        edge_rb=["#00138C", "#001EA0", "#003BDA", "#003BDA"],
        edge_inactive=["#6F8BDA", "#A0B4EA", "#8BA4E4", "#8BA4E4"],
        start_band="#2A5BD0", start_band_text="#D6E2FF", heading="#1C3F94", start_side="#EEF3FD",
        **_CLOSE),
    "Olive": dict(
        label="Olive Green",
        face="#ECE9D8", border="#ACA899", sep="#C5C2B2", menubar_line="#D4D0C8",
        toolbar=("#FEFEFB", "#F2F2E4", "#DFE2C6"),
        sel="#93A070", sel_text="#FFFFFF", sel_inactive="#D4D0C8",
        hover_border="#B6BE98", hover=("#FFFFFF", "#E6E8D6"),
        down_border="#8C9472", down=("#DCDFC8", "#EEF0E2"),
        band=("#5E7A33", "#7E9A4C", "#B4C78C"), band_border="#3F5420",
        pane=("#FFFFFF", "#E3E3CF"), preview=("#F7F7F0", "#E1E2CB"), list_border="#A4B97F",
        header=("#FFFFFF", "#F1F1E4", "#E0E2CC"), header_line="#D3D6BC", header_hover="#F9B119",
        button_border="#37441E", button_hover="#E5A01A", button_default="#8AA05C",
        tab_accent="#FFC83C", group_title="#4E6A1F", group_border="#C9CDAE",
        scroll_track="#F4F3EE", scroll=("#E1E8C8", "#D2DCB1", "#BFCC98"), scroll_border="#A7B582",
        scroll_hover="#EAF0D8", scroll_btn=("#E7EDD3", "#C5D19F"), arrow="#5A6B39",
        title_active=[(0, "#D9E4B5"), (0.08, "#B4C68A"), (0.40, "#A1B575"), (0.88, "#AABF7F"),
                      (0.93, "#AABF7F"), (0.95, "#97AC6C"), (0.96, "#7E9454"), (1, "#7E9454")],
        title_inactive=[(0, "#E3E8D4"), (0.1, "#D3DCBF"), (0.6, "#CAD4B2"), (0.95, "#BFCAA5"),
                        (1, "#B3BF98")],
        title_text="#FFFFFF", title_shadow="#5B6B37", title_text_inactive="#F4F6EC",
        cap=("#C5D6A0", "#86A057"), cap_hover=("#DCE9BB", "#97B266"), cap_down=("#6F8A43", "#B0C487"),
        cap_border="#FFFFFF", cap_glyph="#FFFFFF",
        edge_lt=["#7E9454", "#BFD09A", "#A5B97F", "#A5B97F"],
        edge_rb=["#55673A", "#6B7F47", "#8DA265", "#8DA265"],
        edge_inactive=["#A9B58E", "#D6DEC2", "#C2CDA8", "#C2CDA8"],
        start_band="#6F8B42", start_band_text="#EEF4DD", heading="#4E6A1F", start_side="#F2F5E7",
        **_CLOSE),
    "Silver": dict(
        label="Silver",
        face="#E0DFE3", border="#9D9DA1", sep="#B9B9C3", menubar_line="#C9C9D1",
        toolbar=("#FFFFFF", "#F1F1F5", "#D8D8E1"),
        sel="#B2B4BF", sel_text="#000000", sel_inactive="#D6D6DC",
        hover_border="#A9A9B8", hover=("#FFFFFF", "#E3E3EA"),
        down_border="#8C8CA0", down=("#D2D2DC", "#EBEBF0"),
        band=("#6E6E8C", "#9393AE", "#C9C9DA"), band_border="#55556E",
        pane=("#FFFFFF", "#DCDCE4"), preview=("#F6F6F9", "#DCDCE4"), list_border="#A5ACB5",
        header=("#FFFFFF", "#F1F1F5", "#DCDCE4"), header_line="#C8C8D2", header_hover="#F9B119",
        button_border="#5C5C75", button_hover="#E5A01A", button_default="#8D8DA5",
        tab_accent="#FFC83C", group_title="#3C3C55", group_border="#C2C2CC",
        scroll_track="#F3F3F6", scroll=("#F4F4F8", "#E2E2EA", "#CACAD6"), scroll_border="#A3A3B8",
        scroll_hover="#FFFFFF", scroll_btn=("#F7F7FA", "#CDCDDA"), arrow="#3C3C55",
        title_active=[(0, "#FFFFFF"), (0.08, "#E6E6EE"), (0.40, "#CBCBD8"), (0.88, "#D6D6E1"),
                      (0.93, "#D6D6E1"), (0.95, "#BCBCCB"), (0.96, "#A0A0B4"), (1, "#A0A0B4")],
        title_inactive=[(0, "#FBFBFC"), (0.1, "#EEEEF2"), (0.6, "#E2E2E8"), (0.95, "#D8D8E0"),
                        (1, "#C6C6D0")],
        title_text="#2A2A44", title_shadow="#FFFFFF", title_text_inactive="#8A8A9C",
        cap=("#FFFFFF", "#BABAC9"), cap_hover=("#FFFFFF", "#D3D3DF"), cap_down=("#A8A8BA", "#EDEDF2"),
        cap_border="#8E8EA3", cap_glyph="#3C3C55",
        edge_lt=["#A0A0B4", "#FFFFFF", "#E4E4EB", "#E4E4EB"],
        edge_rb=["#6E6E86", "#8E8EA3", "#C8C8D4", "#C8C8D4"],
        edge_inactive=["#C4C4CE", "#F5F5F8", "#E6E6EC", "#E6E6EC"],
        start_band="#8686A2", start_band_text="#F0F0F6", heading="#3C3C55", start_side="#F2F2F6",
        **_CLOSE),
    "Zune": dict(
        label="Zune",
        face="#EBEBEB", border="#A0A0A0", sep="#C4C4C4", menubar_line="#D0D0D0",
        toolbar=("#FFFFFF", "#F0F0F0", "#D9D9D9"),
        sel="#F27420", sel_text="#FFFFFF", sel_inactive="#D6D6D6",
        hover_border="#F7A35C", hover=("#FFF6EE", "#FCE2CB"),
        down_border="#D9762C", down=("#F8CFA9", "#FDEBDB"),
        band=("#0F0F0F", "#2E2E2E", "#5A5A5A"), band_border="#000000",
        pane=("#FFFFFF", "#DEDEDE"), preview=("#F7F7F7", "#DEDEDE"), list_border="#8C8C8C",
        header=("#FFFFFF", "#F0F0F0", "#DCDCDC"), header_line="#CCCCCC", header_hover="#F27420",
        button_border="#3A3A3A", button_hover="#F27420", button_default="#F27420",
        tab_accent="#F27420", group_title="#D45F10", group_border="#C8C8C8",
        scroll_track="#F2F2F2", scroll=("#E9E9E9", "#D9D9D9", "#C3C3C3"), scroll_border="#9A9A9A",
        scroll_hover="#F4F4F4", scroll_btn=("#EFEFEF", "#C8C8C8"), arrow="#2E2E2E",
        title_active=[(0, "#6A6A6A"), (0.08, "#3A3A3A"), (0.40, "#242424"), (0.88, "#1A1A1A"),
                      (0.93, "#1A1A1A"), (0.95, "#111111"), (0.96, "#000000"), (1, "#000000")],
        title_inactive=[(0, "#8A8A8A"), (0.1, "#6A6A6A"), (0.6, "#5A5A5A"), (0.95, "#4E4E4E"),
                        (1, "#444444")],
        title_text="#FFFFFF", title_shadow="#000000", title_text_inactive="#C8C8C8",
        cap=("#6B6B6B", "#262626"), cap_hover=("#8A8A8A", "#3A3A3A"), cap_down=("#141414", "#555555"),
        cap_border="#A0A0A0", cap_glyph="#FFFFFF",
        close=("#FF9A4D", "#E05A00"), close_hover=("#FFB273", "#F06A10"), close_down=("#C04800", "#FF9A4D"),
        edge_lt=["#000000", "#5A5A5A", "#303030", "#303030"],
        edge_rb=["#000000", "#1C1C1C", "#303030", "#303030"],
        edge_inactive=["#3C3C3C", "#7A7A7A", "#5A5A5A", "#5A5A5A"],
        start_band="#1E1E1E", start_band_text="#F59B5A", heading="#D45F10", start_side="#F4F4F4"),
}
THEME_NAME = "Blue"
THEME = THEMES["Blue"]


def set_theme(name):
    global THEME, THEME_NAME
    THEME_NAME = name if name in THEMES else "Blue"
    THEME = THEMES[THEME_NAME]


def build_stylesheet(res_dir):
    r = res_dir.as_posix()
    T = THEME
    n = THEME_NAME
    return f"""
QMainWindow, QDialog {{ background: {T['face']}; }}
QWidget {{ color: #000000; }}
#composeHead {{ background: {T['face']}; }}
QMenuBar {{ background: {T['face']}; border-bottom: 1px solid {T['menubar_line']}; }}
QMenuBar::item {{ padding: 3px 7px; background: transparent; }}
QMenuBar::item:selected {{ background: {T['sel']}; color: {T['sel_text']}; }}
QMenu {{ background: #FFFFFF; border: 1px solid {T['border']}; padding: 2px; }}
QMenu::item {{ padding: 3px 26px 3px 24px; }}
QMenu::item:selected {{ background: {T['sel']}; color: {T['sel_text']}; }}
QMenu::item:disabled {{ color: {T['border']}; }}
QMenu::separator {{ height: 1px; background: {T['border']}; margin: 3px 2px; }}
QMenu::icon {{ padding-left: 4px; }}

QToolBar {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['toolbar'][0]}, stop:0.6 {T['toolbar'][1]}, stop:1 {T['toolbar'][2]});
           border: none; border-bottom: 1px solid {T['border']}; spacing: 1px; padding: 2px 3px; }}
QToolBar::separator {{ width: 1px; background: {T['sep']}; margin: 4px 4px; }}
QToolBar QToolButton {{ border: 1px solid transparent; border-radius: 3px; padding: 2px 5px; background: transparent; }}
QToolBar QToolButton:hover {{ border: 1px solid {T['hover_border']};
           background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['hover'][0]}, stop:1 {T['hover'][1]}); }}
QToolBar QToolButton:pressed, QToolBar QToolButton:checked {{ border: 1px solid {T['down_border']};
           background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['down'][0]}, stop:1 {T['down'][1]}); }}
QToolBar QToolButton:disabled {{ color: {T['border']}; }}
QToolButton::menu-indicator {{ subcontrol-position: right center; }}

#folderBand {{ background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 {T['band'][0]}, stop:0.55 {T['band'][1]}, stop:1 {T['band'][2]});
              border-bottom: 1px solid {T['band_border']}; }}
#folderBand QLabel {{ color: white; background: transparent; }}
#bandTitle {{ font-size: 13pt; font-weight: bold; font-family: Tahoma, Verdana; }}

#paneHeader {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['pane'][0]}, stop:1 {T['pane'][1]});
              border: 1px solid {T['border']}; border-bottom: none; }}
#paneHeader QToolButton {{ border: 1px solid transparent; padding: 0px 3px; background: transparent; }}
#paneHeader QToolButton:hover {{ border: 1px solid {T['hover_border']}; background: #FFFFFF; border-radius: 2px; }}

QTreeWidget, QListWidget, QTableWidget, QTextBrowser, QTextEdit, QLineEdit, QSpinBox, QComboBox {{
    background: #FFFFFF; border: 1px solid {T['list_border']};
    selection-background-color: {T['sel']}; selection-color: {T['sel_text']}; }}
QTreeWidget::item:selected, QListWidget::item:selected, QTableWidget::item:selected {{
    background: {T['sel']}; color: {T['sel_text']}; }}
QTreeWidget::item:selected:!active, QListWidget::item:selected:!active {{ background: {T['sel_inactive']}; color: #000000; }}
QHeaderView::section {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['header'][0]}, stop:0.8 {T['header'][1]}, stop:1 {T['header'][2]});
    border: none; border-right: 1px solid {T['sep']}; border-bottom: 2px solid {T['header_line']}; padding: 2px 4px; }}
QHeaderView::section:hover {{ border-bottom: 2px solid {T['header_hover']}; background: #FAF9F6; }}

#previewHeader {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['preview'][0]}, stop:1 {T['preview'][1]});
                 border: 1px solid {T['list_border']}; border-bottom: 1px solid {T['border']}; }}
#previewHeader QLabel {{ background: transparent; }}

QStatusBar {{ background: {T['face']}; border-top: 1px solid {T['border']}; }}
QStatusBar::item {{ border: 1px solid {T['sep']}; border-top-color: {T['border']}; margin: 1px 2px; }}
QStatusBar QLabel {{ padding: 0px 6px; }}

QSplitter::handle {{ background: {T['face']}; }}
QSplitter::handle:horizontal {{ width: 4px; }}
QSplitter::handle:vertical {{ height: 4px; }}

QPushButton {{ border: 1px solid {T['button_border']}; border-radius: 3px; padding: 3px 14px; min-width: 60px;
    background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 #FFFFFF, stop:0.85 {T['hover'][1]}, stop:1 {T['down'][0]}); }}
QPushButton:hover {{ border: 1px solid {T['button_hover']};
    background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 #FFFFFF, stop:0.85 {T['toolbar'][1]}, stop:1 {T['hover'][1]}); }}
QPushButton:pressed {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['down'][0]}, stop:1 {T['down'][1]}); }}
QPushButton:default {{ border: 2px solid {T['button_default']}; padding: 2px 13px; }}
QPushButton:disabled {{ color: {T['border']}; border-color: {T['sep']}; }}
#addrButton {{ min-width: 46px; padding: 2px 6px; }}

QTabWidget::pane {{ border: 1px solid #919B9C; background: #FCFCFE; top: -1px; }}
QTabBar::tab {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 #FFFFFF, stop:1 {T['hover'][1]});
    border: 1px solid #919B9C; border-bottom: none; padding: 3px 10px; margin-right: 1px; }}
QTabBar::tab:selected {{ background: #FCFCFE; border-top: 3px solid {T['tab_accent']}; }}
QGroupBox {{ border: 1px solid {T['group_border']}; border-radius: 3px; margin-top: 10px; padding-top: 6px; }}
QGroupBox::title {{ subcontrol-origin: margin; left: 8px; color: {T['group_title']}; padding: 0 3px; }}
QRadioButton::indicator:checked, QCheckBox::indicator:checked {{ }}
QProgressBar {{ border: 1px solid #686868; background: #FFFFFF; height: 14px; border-radius: 2px; text-align: center; }}
QProgressBar::chunk {{ background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 #ACEDAD, stop:0.5 #2BC52F, stop:1 #ACEDAD);
    width: 8px; margin: 1px; }}

QScrollBar:vertical {{ background: {T['scroll_track']}; width: 17px; margin: 17px 0 17px 0; border: none; }}
QScrollBar:horizontal {{ background: {T['scroll_track']}; height: 17px; margin: 0 17px 0 17px; border: none; }}
QScrollBar::handle:vertical {{ min-height: 24px; border: 1px solid {T['scroll_border']}; border-radius: 3px;
    background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 {T['scroll'][0]}, stop:0.5 {T['scroll'][1]}, stop:1 {T['scroll'][2]}); }}
QScrollBar::handle:horizontal {{ min-width: 24px; border: 1px solid {T['scroll_border']}; border-radius: 3px;
    background: qlineargradient(x1:0,y1:0,x2:0,y2:1, stop:0 {T['scroll'][0]}, stop:0.5 {T['scroll'][1]}, stop:1 {T['scroll'][2]}); }}
QScrollBar::handle:hover {{ background: {T['scroll_hover']}; }}
QScrollBar::add-line, QScrollBar::sub-line {{ border: 1px solid {T['scroll_border']}; border-radius: 3px;
    background: qlineargradient(x1:0,y1:0,x2:1,y2:1, stop:0 {T['scroll_btn'][0]}, stop:1 {T['scroll_btn'][1]}); }}
QScrollBar::add-line:vertical {{ subcontrol-origin: margin; subcontrol-position: bottom; height: 16px; }}
QScrollBar::sub-line:vertical {{ subcontrol-origin: margin; subcontrol-position: top; height: 16px; }}
QScrollBar::add-line:horizontal {{ subcontrol-origin: margin; subcontrol-position: right; width: 16px; }}
QScrollBar::sub-line:horizontal {{ subcontrol-origin: margin; subcontrol-position: left; width: 16px; }}
QScrollBar::up-arrow {{ image: url({r}/arr_up_{n}.png); width: 9px; height: 9px; }}
QScrollBar::down-arrow {{ image: url({r}/arr_down_{n}.png); width: 9px; height: 9px; }}
QScrollBar::left-arrow {{ image: url({r}/arr_left_{n}.png); width: 9px; height: 9px; }}
QScrollBar::right-arrow {{ image: url({r}/arr_right_{n}.png); width: 9px; height: 9px; }}
QScrollBar::add-page, QScrollBar::sub-page {{ background: none; }}
"""


def apply_xp_theme(app):
    """(Re)applies the current color scheme to the whole program."""
    T = THEME
    res = APP_DIR / "res"
    res.mkdir(exist_ok=True)
    for name in ("arr_up", "arr_down", "arr_left", "arr_right"):
        path = res / f"{name}_{THEME_NAME}.png"
        if not path.exists():
            make_pixmap(name, 18).save(str(path))
    app.setStyle(QStyleFactory.create("Fusion"))
    pal = QPalette()
    pal.setColor(QPalette.Window, QColor(T["face"]))
    pal.setColor(QPalette.Button, QColor(T["face"]))
    pal.setColor(QPalette.Base, QColor("#FFFFFF"))
    pal.setColor(QPalette.AlternateBase, QColor(T["preview"][0]))
    pal.setColor(QPalette.Highlight, QColor(T["sel"]))
    pal.setColor(QPalette.HighlightedText, QColor(T["sel_text"]))
    pal.setColor(QPalette.WindowText, QColor("#000000"))
    pal.setColor(QPalette.Text, QColor("#000000"))
    pal.setColor(QPalette.ButtonText, QColor("#000000"))
    pal.setColor(QPalette.ToolTipBase, QColor("#FFFFE1"))
    pal.setColor(QPalette.ToolTipText, QColor("#000000"))
    pal.setColor(QPalette.Link, QColor("#0000FF"))
    app.setPalette(pal)
    app.setFont(QFont("Tahoma", 8))
    app.setStyleSheet(build_stylesheet(res))
    for w in app.allWidgets():
        w.update()


class XPTitleBarFilter(QObject):
    """Paints the Windows 11 title bar Luna blue (Win11 22000+ only)."""

    def eventFilter(self, obj, ev):
        if ev.type() == QEvent.Show and isinstance(obj, QWidget) and obj.isWindow() \
                and not obj.property("_xp_done"):
            obj.setProperty("_xp_done", True)
            xp_titlebar(obj)
        return False


def xp_titlebar(widget):
    if sys.platform != "win32":
        return
    try:
        import ctypes
        hwnd = int(widget.winId())

        def cref(h):
            c = QColor(h)
            return c.red() | (c.green() << 8) | (c.blue() << 16)

        T = THEME
        for attr, val in ((35, cref(T["title_active"][2][1])), (36, cref(T["title_text"])),
                          (34, cref(T["edge_lt"][0]))):
            v = ctypes.c_int(val)
            ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, attr, ctypes.byref(v), ctypes.sizeof(v))
    except Exception:
        pass


# --------------------------------------------------------------------------
# Windows XP title bars (drawn by us; the Windows 11 one is switched off)
# --------------------------------------------------------------------------

XP_CHROME = True          # set from Options at startup
TITLE_H = 29
EDGE = 4

# colors come from THEME (see the color schemes above)


class XPCaptionButton(QAbstractButton):
    TIPS = {"min": "Minimize", "max": "Maximize", "restore": "Restore Down", "close": "Close"}

    def __init__(self, kind, parent):
        super().__init__(parent)
        self.kind = kind
        self.setFixedSize(21, 21)
        self.setAttribute(Qt.WA_Hover)
        self.setFocusPolicy(Qt.NoFocus)
        self.setCursor(Qt.ArrowCursor)
        self.setToolTip(self.TIPS[kind])

    def set_kind(self, kind):
        self.kind = kind
        self.setToolTip(self.TIPS[kind])
        self.update()

    def enterEvent(self, ev):
        self.update()
        super().enterEvent(ev)

    def leaveEvent(self, ev):
        self.update()
        super().leaveEvent(ev)

    def paintEvent(self, ev):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing)
        hover, down = self.underMouse(), self.isDown()
        if not self.window().isActiveWindow() and not hover:
            p.setOpacity(0.7)
        T = THEME
        base = "close" if self.kind == "close" else "cap"
        c0, c1 = T[base + "_down"] if down else T[base + "_hover"] if hover else T[base]
        g = QLinearGradient(0, 0, 21, 21)
        g.setColorAt(0, QColor(c0))
        g.setColorAt(1, QColor(c1))
        p.setPen(QPen(QColor(T["cap_border"]), 1))
        p.setBrush(QBrush(g))
        p.drawRoundedRect(QRectF(0.5, 0.5, 20, 20), 3, 3)
        white = QColor("#FFFFFF" if self.kind == "close" else T["cap_glyph"])
        if self.kind == "min":
            p.fillRect(QRectF(5, 13, 7, 3), white)
        elif self.kind == "max":
            p.setBrush(Qt.NoBrush)
            p.setPen(QPen(white, 1))
            p.drawRect(QRectF(5.5, 5.5, 10, 10))
            p.fillRect(QRectF(5, 5, 11, 3), white)
        elif self.kind == "restore":
            p.setPen(QPen(white, 1))
            p.setBrush(Qt.NoBrush)
            p.drawRect(QRectF(8.5, 4.5, 8, 7))
            p.fillRect(QRectF(8, 4, 9, 2), white)
            p.setBrush(QColor(c1))
            p.drawRect(QRectF(4.5, 8.5, 8, 7))
            p.fillRect(QRectF(4, 8, 9, 2), white)
        else:
            p.setPen(_pen(white.name(), 2.4))
            p.drawLine(QPointF(6.5, 6.5), QPointF(14.5, 14.5))
            p.drawLine(QPointF(14.5, 6.5), QPointF(6.5, 14.5))


class XPTitleBar(QWidget):
    def __init__(self, chrome):
        super().__init__(chrome.win)
        self.chrome = chrome
        self.win = chrome.win
        self.setMouseTracking(True)
        self.btn_min = XPCaptionButton("min", self)
        self.btn_max = XPCaptionButton("max", self)
        self.btn_close = XPCaptionButton("close", self)
        self.btn_min.clicked.connect(self.win.showMinimized)
        self.btn_max.clicked.connect(chrome.toggle_max)
        self.btn_close.clicked.connect(self.win.close)
        self.btn_min.setVisible(chrome.full)
        self.btn_max.setVisible(chrome.full)

    def resizeEvent(self, ev):
        x = self.width() - 5 - 21
        self.btn_close.move(x, 4)
        for b in (self.btn_max, self.btn_min):
            if b.isVisibleTo(self):
                x -= 23
                b.move(x, 4)
        self.text_right = x - 6

    def paintEvent(self, ev):
        p = QPainter(self)
        active = self.win.isActiveWindow()
        g = QLinearGradient(0, 0, 0, self.height())
        T = THEME
        for pos, col in (T["title_active"] if active else T["title_inactive"]):
            g.setColorAt(pos, QColor(col))
        p.fillRect(self.rect(), QBrush(g))
        ic = self.win.windowIcon()
        if not ic.isNull():
            ic.paint(p, QRect(6, (self.height() - 16) // 2, 16, 16))
        f = QFont("Trebuchet MS")
        f.setBold(True)
        f.setPixelSize(13)
        p.setFont(f)
        right = getattr(self, "text_right", self.width() - 80)
        rect = QRect(28, 0, max(0, right - 28), self.height())
        text = QFontMetrics(f).elidedText(self.win.windowTitle(), Qt.ElideRight, rect.width())
        if active:
            p.setPen(QColor(T["title_shadow"]))
            p.drawText(rect.translated(1, 1), Qt.AlignVCenter | Qt.AlignLeft, text)
        p.setPen(QColor(T["title_text"] if active else T["title_text_inactive"]))
        p.drawText(rect, Qt.AlignVCenter | Qt.AlignLeft, text)

    def _edges(self, pos):
        if self.chrome.maxed or not self.chrome.resizable or pos.y() >= EDGE:
            return None
        e = Qt.TopEdge
        if pos.x() < 10:
            e = e | Qt.LeftEdge
        elif pos.x() > self.width() - 10:
            e = e | Qt.RightEdge
        return e

    def mouseMoveEvent(self, ev):
        e = self._edges(ev.position().toPoint())
        if e is None:
            self.unsetCursor()
        elif e == Qt.TopEdge:
            self.setCursor(Qt.SizeVerCursor)
        else:
            self.setCursor(Qt.SizeFDiagCursor if ev.position().x() < 10 else Qt.SizeBDiagCursor)

    def mousePressEvent(self, ev):
        pos = ev.position().toPoint()
        if ev.button() == Qt.LeftButton:
            if pos.x() < 26:                         # the little icon opens the window menu
                self.chrome.system_menu(self.mapToGlobal(QPoint(0, self.height())))
                return
            e = self._edges(pos)
            handle = self.win.windowHandle()
            if handle is None:
                return
            if e is not None:
                handle.startSystemResize(e)
            elif not self.chrome.maxed:              # like XP: a maximized window can't be dragged
                handle.startSystemMove()

    def mouseDoubleClickEvent(self, ev):
        if ev.button() == Qt.LeftButton:
            if ev.position().x() < 26:
                self.win.close()
            elif self.chrome.full:
                self.chrome.toggle_max()

    def contextMenuEvent(self, ev):
        self.chrome.system_menu(ev.globalPos())


class XPEdge(QWidget):
    """The blue window border on the left, right and bottom; also the resize handles."""

    def __init__(self, chrome, side):
        super().__init__(chrome.win)
        self.chrome = chrome
        self.side = side
        self.setMouseTracking(True)

    def _edges(self, pos):
        if not self.chrome.resizable:
            return None
        c = 16
        if self.side == "l":
            return Qt.LeftEdge | Qt.BottomEdge if pos.y() > self.height() - c else Qt.LeftEdge
        if self.side == "r":
            return Qt.RightEdge | Qt.BottomEdge if pos.y() > self.height() - c else Qt.RightEdge
        if pos.x() < c:
            return Qt.LeftEdge | Qt.BottomEdge
        if pos.x() > self.width() - c:
            return Qt.RightEdge | Qt.BottomEdge
        return Qt.BottomEdge

    def mouseMoveEvent(self, ev):
        e = self._edges(ev.position().toPoint())
        cursors = {Qt.LeftEdge: Qt.SizeHorCursor, Qt.RightEdge: Qt.SizeHorCursor,
                   Qt.BottomEdge: Qt.SizeVerCursor, Qt.LeftEdge | Qt.BottomEdge: Qt.SizeBDiagCursor,
                   Qt.RightEdge | Qt.BottomEdge: Qt.SizeFDiagCursor}
        if e is None:
            self.unsetCursor()
        else:
            for k, cur in cursors.items():
                if e == k:
                    self.setCursor(cur)

    def mousePressEvent(self, ev):
        e = self._edges(ev.position().toPoint())
        handle = self.chrome.win.windowHandle()
        if ev.button() == Qt.LeftButton and e is not None and handle is not None:
            handle.startSystemResize(e)

    def paintEvent(self, ev):
        p = QPainter(self)
        active = self.chrome.win.isActiveWindow()
        w, h = self.width(), self.height()
        if self.side == "l":
            cols = THEME["edge_lt"] if active else THEME["edge_inactive"]
            for i, c in enumerate(cols):
                p.fillRect(i, 0, 1, h, QColor(c))
        elif self.side == "r":
            cols = THEME["edge_rb"] if active else THEME["edge_inactive"]
            for i, c in enumerate(cols):
                p.fillRect(w - 1 - i, 0, 1, h, QColor(c))
        else:
            cols = THEME["edge_rb"] if active else THEME["edge_inactive"]
            for i, c in enumerate(cols):
                p.fillRect(0, h - 1 - i, w, 1, QColor(c))
            lt = THEME["edge_lt"] if active else THEME["edge_inactive"]
            for i, c in enumerate(lt[:EDGE]):          # keep the left stripes running to the corner
                p.fillRect(i, 0, 1, h - 1 - i, QColor(c))
            for i, c in enumerate(cols):
                p.fillRect(w - 1 - i, 0, 1, h, QColor(c))


class XPChrome(QObject):
    def __init__(self, win, full):
        super().__init__(win)
        self.win = win
        self.full = full                        # main windows get minimize/maximize
        self.resizable = not isinstance(win, (QMessageBox, QInputDialog))
        self.maxed = False
        self.normal_geo = None
        self._shown = False
        self.title = XPTitleBar(self)
        self.edges = [XPEdge(self, s) for s in "lrb"]
        self.close_key = QShortcut(QKeySequence("Alt+F4"), win)
        self.close_key.activated.connect(win.close)
        win.installEventFilter(self)
        self.apply_margins()

    def apply_margins(self):
        e = 0 if self.maxed else EDGE
        self.win.setContentsMargins(e, TITLE_H, e, e)
        for x in self.edges:
            x.setVisible(not self.maxed)
        self.title.btn_max.set_kind("restore" if self.maxed else "max")
        self.place()

    def place(self):
        w, h = self.win.width(), self.win.height()
        self.title.setGeometry(0, 0, w, TITLE_H)
        self.title.raise_()
        left, right, bottom = self.edges
        left.setGeometry(0, TITLE_H, EDGE, h - TITLE_H)
        right.setGeometry(w - EDGE, TITLE_H, EDGE, h - TITLE_H)
        bottom.setGeometry(0, h - EDGE, w, EDGE)
        for x in self.edges:
            x.raise_()

    def toggle_max(self):
        if not self.full:
            return
        if self.maxed:
            self.maxed = False
            if self.normal_geo:
                self.win.setGeometry(self.normal_geo)
        else:
            self.normal_geo = self.win.geometry()
            self.maxed = True
            screen = self.win.screen() or QApplication.primaryScreen()
            self.win.setGeometry(screen.availableGeometry())
        self.apply_margins()

    def system_menu(self, pos):
        m = QMenu(self.win)
        restore = m.addAction("&Restore", self.toggle_max)
        restore.setEnabled(self.maxed)
        if self.full:
            m.addAction("Mi&nimize", self.win.showMinimized)
            mx = m.addAction("Ma&ximize", self.toggle_max)
            mx.setEnabled(not self.maxed)
        m.addSeparator()
        close = m.addAction("&Close\tAlt+F4", self.win.close)
        m.setDefaultAction(close)
        m.exec(pos)

    def _native_tweaks(self):
        if sys.platform != "win32":
            return
        try:
            import ctypes
            hwnd = int(self.win.winId())
            u32 = ctypes.windll.user32
            if self.full:     # lets a click on the taskbar button minimize/restore the window
                style = u32.GetWindowLongW(hwnd, -16)
                u32.SetWindowLongW(hwnd, -16, style | 0x00020000)
            v = ctypes.c_int(3)  # DWMWCP_ROUNDSMALL: softly rounded corners
            ctypes.windll.dwmapi.DwmSetWindowAttribute(hwnd, 33, ctypes.byref(v), ctypes.sizeof(v))
        except Exception:
            pass

    def _absorb_native_max(self):
        if self.win.isMaximized():               # Win+Up or Snap: use our own maximize instead
            self.win.showNormal()
            if not self.maxed:
                self.toggle_max()

    def eventFilter(self, obj, ev):
        if obj is self.win:
            t = ev.type()
            if t in (QEvent.Resize, QEvent.Show):
                self.place()
                if t == QEvent.Show and not self._shown:
                    self._shown = True
                    self._native_tweaks()
            elif t in (QEvent.WindowTitleChange, QEvent.WindowIconChange, QEvent.ActivationChange):
                self.title.update()
                for b in (self.title.btn_min, self.title.btn_max, self.title.btn_close):
                    b.update()
                for e in self.edges:
                    e.update()
            elif t == QEvent.WindowStateChange and self.full and self.win.isMaximized():
                QTimer.singleShot(0, self._absorb_native_max)
        return False


def xp_frame(win):
    """Give a window the XP title bar and border (when turned on in Options)."""
    if not XP_CHROME or getattr(win, "_xp_chrome", None):
        return
    win.setWindowFlags(win.windowFlags() | Qt.FramelessWindowHint)
    win._xp_chrome = XPChrome(win, isinstance(win, QMainWindow))


class XPMsg:
    """Message boxes with the XP title bar (same calls as QMessageBox.question & co.)."""

    @staticmethod
    def _run(kind, parent, title, text, buttons, default=None):
        mb = QMessageBox(kind, title, text, buttons, parent)
        if default is not None:
            mb.setDefaultButton(default)
        xp_frame(mb)
        mb.exec()
        b = mb.clickedButton()
        return mb.standardButton(b) if b is not None else QMessageBox.Cancel

    @staticmethod
    def question(parent, title, text, buttons=QMessageBox.Yes | QMessageBox.No, default=None):
        return XPMsg._run(QMessageBox.Question, parent, title, text, buttons, default)

    @staticmethod
    def information(parent, title, text, buttons=QMessageBox.Ok, default=None):
        return XPMsg._run(QMessageBox.Information, parent, title, text, buttons, default)

    @staticmethod
    def warning(parent, title, text, buttons=QMessageBox.Ok, default=None):
        return XPMsg._run(QMessageBox.Warning, parent, title, text, buttons, default)

    @staticmethod
    def critical(parent, title, text, buttons=QMessageBox.Ok, default=None):
        return XPMsg._run(QMessageBox.Critical, parent, title, text, buttons, default)

    @staticmethod
    def about(parent, title, text):
        mb = QMessageBox(parent)
        mb.setWindowTitle(title)
        mb.setText(text)
        mb.setIconPixmap(make_pixmap("app", 48))
        xp_frame(mb)
        mb.exec()


def xp_get_text(parent, title, label, mode=QLineEdit.Normal, text=""):
    d = QInputDialog(parent)
    d.setWindowTitle(title)
    d.setLabelText(label)
    d.setTextEchoMode(mode)
    d.setTextValue(text)
    xp_frame(d)
    ok = bool(d.exec())
    return d.textValue(), ok


def xp_get_item(parent, title, label, items, current=0, editable=False):
    d = QInputDialog(parent)
    d.setWindowTitle(title)
    d.setLabelText(label)
    d.setComboBoxItems(items)
    d.setComboBoxEditable(editable)
    if items:
        d.setTextValue(items[current])
    xp_frame(d)
    ok = bool(d.exec())
    return d.textValue(), ok


# --------------------------------------------------------------------------
# Config, passwords, mail helpers
# --------------------------------------------------------------------------

DEFAULT_SETTINGS = {
    "check_enabled": True, "check_minutes": 30, "play_sound": True, "read_delay": 5,
    "send_immediately": True, "fetch_limit": 300, "start_in_inbox": False, "block_images": True,
    "xp_titlebars": True, "theme": "Blue",
    "show_preview": True, "show_folders": True, "show_contacts": True,
    "show_statusbar": True, "show_toolbar": True,
}


class Config:
    def __init__(self):
        self.path = APP_DIR / "config.json"
        self.data = {"accounts": [], "settings": dict(DEFAULT_SETTINGS)}
        if self.path.exists():
            try:
                loaded = json.loads(self.path.read_text("utf-8"))
                self.data["accounts"] = loaded.get("accounts", [])
                self.data["settings"].update(loaded.get("settings", {}))
                for k, v in loaded.items():
                    if k not in ("accounts", "settings"):
                        self.data[k] = v
            except Exception:
                pass

    @property
    def accounts(self):
        return self.data["accounts"]

    def get(self, key):
        return self.data["settings"].get(key, DEFAULT_SETTINGS.get(key))

    def set(self, key, value):
        self.data["settings"][key] = value

    def account(self, acct_id):
        for a in self.accounts:
            if a.get("id") == acct_id:
                return a
        return None

    def default_account(self):
        for a in self.accounts:
            if a.get("default"):
                return a
        return self.accounts[0] if self.accounts else None

    def save(self):
        tmp = self.path.with_suffix(".tmp")
        tmp.write_text(json.dumps(self.data, indent=2), "utf-8")
        tmp.replace(self.path)


def set_password(acct, pw):
    if keyring:
        try:
            keyring.set_password("ExpressMail", acct["id"], pw)
            acct["pw_in_keyring"] = True
            acct.pop("password_b64", None)
            return
        except Exception:
            pass
    acct["pw_in_keyring"] = False
    acct["password_b64"] = base64.b64encode(pw.encode("utf-8")).decode("ascii")


def get_password(acct):
    if acct.get("pw_in_keyring") and keyring:
        try:
            v = keyring.get_password("ExpressMail", acct["id"])
            if v is not None:
                return v
        except Exception:
            pass
    b = acct.get("password_b64")
    return base64.b64decode(b).decode("utf-8") if b else ""


def parse_msg(raw):
    return BytesParser(policy=policy.default).parsebytes(raw or b"")


def hdr(m, name):
    try:
        v = m.get(name)
        return str(v).strip() if v is not None else ""
    except Exception:
        try:
            return str(m.get_all(name, [""])[0])
        except Exception:
            return ""


def parse_addresses(*fields):
    """[(name, address), ...] from header strings. Each field is parsed on its own:
    newer Pythons discard the whole list if any field is blank. Accepts ; or , separators."""
    out = []
    for f in fields:
        f = (f or "").replace(";", ",").strip().strip(",").strip()
        if not f:
            continue
        for name, addr in getaddresses([f]):
            if addr and "@" in addr:
                out.append((name, addr))
    return out


def display_name(addr_field):
    pairs = parse_addresses(addr_field)
    names = [n or a for n, a in pairs if n or a]
    return ", ".join(names) if names else addr_field


def msg_timestamp(m):
    try:
        return parsedate_to_datetime(hdr(m, "Date")).timestamp()
    except Exception:
        return time.time()


def fmt_date(ts):
    dt = datetime.fromtimestamp(ts)
    return f"{dt.month}/{dt.day}/{dt.year} {dt.strftime('%I:%M %p').lstrip('0')}"


def msg_priority(m):
    xp = hdr(m, "X-Priority")[:1]
    imp = hdr(m, "Importance").lower()
    if xp in ("1", "2") or imp == "high":
        return 1
    if xp in ("4", "5") or imp == "low":
        return 5
    return 3


def attachments_of(m):
    try:
        return list(m.iter_attachments()) if m.is_multipart() else []
    except Exception:
        return []


def summarize(raw):
    m = parse_msg(raw)
    return {
        "sender": hdr(m, "From"),
        "recipients": ", ".join(x for x in (hdr(m, "To"), hdr(m, "Cc")) if x),
        "subject": hdr(m, "Subject"),
        "ts": msg_timestamp(m),
        "has_attach": 1 if attachments_of(m) else 0,
        "priority": msg_priority(m),
    }


def _part_text(part):
    try:
        return part.get_content()
    except Exception:
        payload = part.get_payload(decode=True) or b""
        return payload.decode(part.get_content_charset() or "utf-8", "replace")


URL_RE = re.compile(r"(https?://[^\s<>\"']+)")


def body_html(m):
    try:
        part = m.get_body(preferencelist=("html", "plain"))
    except Exception:
        part = None
    if part is None:
        if not m.is_multipart() and m.get_content_maintype() == "text":
            part = m
        else:
            return "<p style='color:#808080'><i>(This message has no text.)</i></p>"
    text = _part_text(part)
    if part.get_content_type() == "text/html":
        return text
    esc = URL_RE.sub(r'<a href="\1">\1</a>', html.escape(text))
    return ("<div style='font-family:Arial; font-size:10pt; white-space:pre-wrap'>"
            f"{esc}</div>")


def body_plain(m):
    try:
        part = m.get_body(preferencelist=("plain", "html"))
    except Exception:
        part = None
    if part is None:
        return ""
    text = _part_text(part)
    if part.get_content_type() == "text/html":
        doc = QTextDocument()
        doc.setHtml(text)
        return doc.toPlainText()
    return text


# --------------------------------------------------------------------------
# Local message store (SQLite)
# --------------------------------------------------------------------------

SCHEMA = """
CREATE TABLE IF NOT EXISTS folders(name TEXT PRIMARY KEY, special INTEGER DEFAULT 0,
                                   sort INTEGER DEFAULT 100);
CREATE TABLE IF NOT EXISTS messages(
    id INTEGER PRIMARY KEY AUTOINCREMENT, folder TEXT, account TEXT, remote_uid TEXT,
    sender TEXT, recipients TEXT, subject TEXT, ts REAL, has_attach INTEGER DEFAULT 0,
    is_read INTEGER DEFAULT 0, flagged INTEGER DEFAULT 0, priority INTEGER DEFAULT 3,
    raw BLOB);
CREATE UNIQUE INDEX IF NOT EXISTS ux_remote ON messages(account, remote_uid)
    WHERE remote_uid IS NOT NULL;
CREATE INDEX IF NOT EXISTS ix_folder ON messages(folder);
CREATE TABLE IF NOT EXISTS contacts(id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT,
    email TEXT, phone TEXT, notes TEXT);
"""

LIST_COLS = "id, folder, account, sender, recipients, subject, ts, has_attach, is_read, flagged, priority"


class Store:
    def __init__(self, path):
        self.path = str(path)
        self.db = sqlite3.connect(self.path, timeout=15)
        self.db.row_factory = sqlite3.Row
        self.db.executescript(SCHEMA)
        for i, name in enumerate(SPECIAL_FOLDERS):
            self.db.execute("INSERT OR IGNORE INTO folders(name, special, sort) VALUES(?,1,?)",
                            (name, i))
        self.db.commit()

    @staticmethod
    def _q(ids):
        return ",".join("?" * len(ids))

    def is_empty(self):
        return self.db.execute("SELECT COUNT(*) FROM messages").fetchone()[0] == 0

    def add_message(self, folder, raw, account=None, remote_uid=None, is_read=0):
        s = summarize(raw)
        try:
            cur = self.db.execute(
                "INSERT INTO messages(folder, account, remote_uid, sender, recipients, subject, ts,"
                " has_attach, is_read, priority, raw) VALUES(?,?,?,?,?,?,?,?,?,?,?)",
                (folder, account, remote_uid, s["sender"], s["recipients"], s["subject"],
                 s["ts"], s["has_attach"], is_read, s["priority"], raw))
            self.db.commit()
            return cur.lastrowid
        except sqlite3.IntegrityError:
            return None

    def list(self, folder, hide_read=False):
        sql = f"SELECT {LIST_COLS} FROM messages WHERE folder=?"
        if hide_read:
            sql += " AND is_read=0"
        return self.db.execute(sql + " ORDER BY ts DESC", (folder,)).fetchall()

    def search(self, term):
        like = f"%{term}%"
        return self.db.execute(
            f"SELECT {LIST_COLS} FROM messages WHERE sender LIKE ? OR recipients LIKE ? "
            "OR subject LIKE ? ORDER BY ts DESC", (like, like, like)).fetchall()

    def get(self, mid):
        return self.db.execute("SELECT * FROM messages WHERE id=?", (mid,)).fetchone()

    def counts(self):
        out = {}
        for r in self.db.execute("SELECT folder, COUNT(*) AS n, SUM(is_read=0) AS u "
                                 "FROM messages GROUP BY folder"):
            out[r["folder"]] = r["n"] if r["folder"] in ("Outbox", "Drafts") else (r["u"] or 0)
        return out

    def set_read(self, ids, value):
        if ids:
            self.db.execute(f"UPDATE messages SET is_read=? WHERE id IN ({self._q(ids)})",
                            [int(value), *ids])
            self.db.commit()

    def mark_all_read(self, folder):
        self.db.execute("UPDATE messages SET is_read=1 WHERE folder=?", (folder,))
        self.db.commit()

    def set_flag(self, ids, value):
        if ids:
            self.db.execute(f"UPDATE messages SET flagged=? WHERE id IN ({self._q(ids)})",
                            [int(value), *ids])
            self.db.commit()

    def move(self, ids, folder):
        if ids:
            self.db.execute(f"UPDATE messages SET folder=? WHERE id IN ({self._q(ids)})",
                            [folder, *ids])
            self.db.commit()

    def delete(self, ids):
        if ids:
            self.db.execute(f"DELETE FROM messages WHERE id IN ({self._q(ids)})", list(ids))
            self.db.commit()

    def empty_folder(self, folder):
        self.db.execute("DELETE FROM messages WHERE folder=?", (folder,))
        self.db.commit()

    def known_remote(self, account):
        return {r[0] for r in self.db.execute(
            "SELECT remote_uid FROM messages WHERE account=? AND remote_uid IS NOT NULL", (account,))}

    def folders(self):
        return self.db.execute("SELECT name, special FROM folders ORDER BY sort, name").fetchall()

    def add_folder(self, name):
        self.db.execute("INSERT INTO folders(name, special, sort) VALUES(?,0,100)", (name,))
        self.db.commit()

    def rename_folder(self, old, new):
        self.db.execute("UPDATE folders SET name=? WHERE name=?", (new, old))
        self.db.execute("UPDATE messages SET folder=? WHERE folder=?", (new, old))
        self.db.commit()

    def delete_folder(self, name):
        self.db.execute("UPDATE messages SET folder='Deleted Items' WHERE folder=?", (name,))
        self.db.execute("DELETE FROM folders WHERE name=? AND special=0", (name,))
        self.db.commit()

    # contacts
    def contacts(self):
        return self.db.execute("SELECT * FROM contacts ORDER BY name COLLATE NOCASE").fetchall()

    def save_contact(self, cid, name, email, phone, notes):
        if cid:
            self.db.execute("UPDATE contacts SET name=?, email=?, phone=?, notes=? WHERE id=?",
                            (name, email, phone, notes, cid))
        else:
            self.db.execute("INSERT INTO contacts(name, email, phone, notes) VALUES(?,?,?,?)",
                            (name, email, phone, notes))
        self.db.commit()

    def delete_contact(self, cid):
        self.db.execute("DELETE FROM contacts WHERE id=?", (cid,))
        self.db.commit()


def welcome_raw():
    m = EmailMessage()
    m["From"] = formataddr((f"{APP_NAME} Team", "welcome@expressmail.invalid"))
    m["To"] = formataddr(("New User", "you@localhost"))
    m["Subject"] = f"Welcome to {APP_NAME}"
    m["Date"] = formatdate(localtime=True)
    m.set_content(f"Welcome to {APP_NAME}!")
    m.add_alternative(f"""
<div style="font-family:Tahoma; font-size:9pt">
<p style="font-size:16pt; color:#1F4FC2"><b>{APP_NAME}</b></p>
<p>The e-mail program you remember, rebuilt for today. Everything is where you left it:
Folders on the left, Contacts underneath, your messages up top and the Preview Pane below.</p>
<p><b>Getting connected</b></p>
<ul>
<li>Choose <b>Tools &gt; Accounts...</b> and click <b>Add</b>.</li>
<li>Pick your provider (Gmail, Yahoo, iCloud, AOL, Fastmail) or enter your IMAP and SMTP servers.</li>
<li>Gmail, Yahoo and iCloud require an <b>app password</b> - create one in your account's
security settings and use it instead of your normal password.</li>
<li>Click <b>Send/Recv</b> (Ctrl+M) to download your mail.</li>
</ul>
<p><b>Good to know</b></p>
<ul>
<li>Mail is copied to this computer and left on the server, so your phone still sees it.</li>
<li>Pictures from the internet are never downloaded, so senders can't tell you opened their mail.</li>
<li>Dangerous attachments (.exe, .vbs, .js and friends) can be saved but never opened directly.</li>
</ul>
<p>Enjoy!<br>The {APP_NAME} Team</p></div>""", subtype="html")
    return m.as_bytes()


# --------------------------------------------------------------------------
# Network: IMAP receive, SMTP send (runs in a worker thread)
# --------------------------------------------------------------------------

# ---- "Sign in with Google" (OAuth 2.0 for installed apps, loopback + PKCE) ----

GOOGLE_AUTH_URL = "https://accounts.google.com/o/oauth2/v2/auth"
GOOGLE_TOKEN_URL = "https://oauth2.googleapis.com/token"
GOOGLE_SCOPES = "https://mail.google.com/ openid email profile"
GOOGLE_CLIENT_FILE = APP_DIR / "google_client.json"
GOOGLE_CONSOLE_URL = "https://console.cloud.google.com/auth/overview"


class OAuthError(Exception):
    def __init__(self, code, message):
        super().__init__(message)
        self.code = code


def google_client():
    """The OAuth client (ID + secret) registered by the user, or None."""
    try:
        d = json.loads(GOOGLE_CLIENT_FILE.read_text("utf-8"))
        if d.get("client_id") and d.get("client_secret"):
            return d
    except Exception:
        pass
    return None


def save_google_client(client_id, client_secret):
    GOOGLE_CLIENT_FILE.write_text(json.dumps({"client_id": client_id.strip(),
                                              "client_secret": client_secret.strip()}, indent=2), "utf-8")


def read_client_secret_json(path):
    """Reads the client_secret_....json file downloaded from Google Cloud."""
    d = json.loads(Path(path).read_text("utf-8"))
    inner = d.get("installed") or d.get("web") or d
    return inner.get("client_id", ""), inner.get("client_secret", "")


def _token_request(params):
    data = urllib.parse.urlencode(params).encode()
    req = urllib.request.Request(GOOGLE_TOKEN_URL, data=data,
                                 headers={"Content-Type": "application/x-www-form-urlencoded"})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            return json.loads(r.read())
    except urllib.error.HTTPError as e:
        try:
            body = json.loads(e.read())
        except Exception:
            body = {}
        raise OAuthError(body.get("error", ""), body.get("error_description") or str(e))


def jwt_claims(id_token):
    try:
        payload = id_token.split(".")[1]
        payload += "=" * (-len(payload) % 4)
        return json.loads(base64.urlsafe_b64decode(payload))
    except Exception:
        return {}


_TOKEN_CACHE = {}
_TOKEN_LOCK = threading.Lock()


def remember_access_token(acct_id, token, expires_in):
    with _TOKEN_LOCK:
        _TOKEN_CACHE[acct_id] = (token, time.time() + int(expires_in or 3600))


def google_access_token(acct):
    """A fresh access token, refreshed with the stored refresh token when needed."""
    with _TOKEN_LOCK:
        cached = _TOKEN_CACHE.get(acct["id"])
        if cached and cached[1] > time.time() + 60:
            return cached[0]
        client = google_client()
        if not client:
            raise OAuthError("no_client", "Google sign-in isn't set up on this computer. Open Tools > "
                                          "Accounts > Properties and click 'Sign in with Google'.")
        refresh = get_password(acct)
        if not refresh:
            raise OAuthError("no_token", "You're not signed in to Google. Open Tools > Accounts > "
                                         "Properties and click 'Sign in with Google'.")
        try:
            r = _token_request({"client_id": client["client_id"], "client_secret": client["client_secret"],
                                "refresh_token": refresh, "grant_type": "refresh_token"})
        except OAuthError as e:
            if e.code in ("invalid_grant", "invalid_client", "unauthorized_client"):
                raise OAuthError(e.code, "Your Google sign-in has expired or was removed. Open Tools > "
                                         "Accounts > Properties and click 'Sign in with Google' again.")
            raise
        _TOKEN_CACHE[acct["id"]] = (r["access_token"], time.time() + int(r.get("expires_in", 3600)))
        return r["access_token"]


def xoauth2_string(email, token):
    return f"user={email}\x01auth=Bearer {token}\x01\x01"


SIGNED_IN_PAGE = """<!doctype html><html><head><meta charset="utf-8"><title>{app}</title></head>
<body style="font-family:Tahoma,Verdana,sans-serif;background:#ECE9D8;margin:0">
<div style="background:linear-gradient(90deg,#1F4FC2,#7EA6EE);color:#fff;padding:14px 20px;
font-size:20px;font-weight:bold">{app}</div>
<div style="background:#fff;border:1px solid #7F9DB9;margin:24px;padding:20px;font-size:14px">
<p style="font-size:16px"><b>{title}</b></p><p>{text}</p></div></body></html>"""


class GoogleLogin:
    """Opens Google's sign-in page in the browser and catches the reply on 127.0.0.1."""

    def __init__(self, client, login_hint=""):
        self.client = client
        self.code = None
        self.error = None
        self.cancelled = False
        self.state = secrets.token_urlsafe(16)
        self.verifier = secrets.token_urlsafe(64)
        challenge = base64.urlsafe_b64encode(
            hashlib.sha256(self.verifier.encode()).digest()).rstrip(b"=").decode()
        outer = self

        class Handler(BaseHTTPRequestHandler):
            def do_GET(self):
                q = urllib.parse.parse_qs(urllib.parse.urlparse(self.path).query)
                if "code" not in q and "error" not in q:
                    self.send_response(404)
                    self.end_headers()
                    return
                if q.get("state", [""])[0] != outer.state:
                    outer.error = "state_mismatch"
                elif "error" in q:
                    outer.error = q["error"][0]
                else:
                    outer.code = q["code"][0]
                if outer.code:
                    title, text = "You're signed in.", f"You can close this window and go back to {APP_NAME}."
                else:
                    title, text = "Sign-in didn't finish.", f"Go back to {APP_NAME} and try again."
                page = SIGNED_IN_PAGE.format(app=APP_NAME, title=title, text=text).encode()
                self.send_response(200)
                self.send_header("Content-Type", "text/html; charset=utf-8")
                self.send_header("Content-Length", str(len(page)))
                self.end_headers()
                self.wfile.write(page)

            def log_message(self, *args):
                pass

        self.server = HTTPServer(("127.0.0.1", 0), Handler)
        self.server.timeout = 0.5
        self.redirect_uri = f"http://127.0.0.1:{self.server.server_address[1]}"
        params = {"client_id": client["client_id"], "redirect_uri": self.redirect_uri,
                  "response_type": "code", "scope": GOOGLE_SCOPES, "access_type": "offline",
                  "prompt": "consent", "code_challenge": challenge, "code_challenge_method": "S256",
                  "state": self.state}
        if login_hint:
            params["login_hint"] = login_hint
        self.url = GOOGLE_AUTH_URL + "?" + urllib.parse.urlencode(params)
        self.thread = threading.Thread(target=self._serve, daemon=True)

    def start(self):
        self.thread.start()
        self.open_browser()

    def open_browser(self):
        webbrowser.open(self.url)

    def _serve(self):
        try:
            while not self.cancelled and self.code is None and self.error is None:
                self.server.handle_request()
        finally:
            self.server.server_close()

    def done(self):
        return self.code is not None or self.error is not None

    def exchange(self):
        return _token_request({"code": self.code, "client_id": self.client["client_id"],
                               "client_secret": self.client["client_secret"],
                               "redirect_uri": self.redirect_uri, "grant_type": "authorization_code",
                               "code_verifier": self.verifier})


def friendly_error(e):
    """Turns raw server replies into something a person can act on."""
    s = str(e)
    if isinstance(e, OAuthError):
        return s
    if "Application-specific password required" in s:
        return ("Gmail won't accept your normal password. Open Tools > Accounts > Properties and click "
                "'Sign in with Google' (or enter a Gmail app password).")
    if "AUTHENTICATIONFAILED" in s or "Invalid credentials" in s or "535" in s:
        return ("The server rejected your user name or password. Check them in Tools > Accounts > "
                f"Properties.  (Server said: {s})")
    if "getaddrinfo" in s or "Name or service not known" in s or "timed out" in s:
        return f"Couldn't reach the server. Check your internet connection and the server name.  ({s})"
    return s


def imap_connect(acct):
    host, port = acct["imap_host"], int(acct.get("imap_port") or 993)
    if acct.get("imap_ssl", True):
        M = imaplib.IMAP4_SSL(host, port, ssl_context=ssl.create_default_context(), timeout=30)
    else:
        M = imaplib.IMAP4(host, port, timeout=30)
        try:
            M.starttls(ssl_context=ssl.create_default_context())
        except Exception:
            pass
    if acct.get("auth_type") == "oauth_google":
        auth = xoauth2_string(acct["email"], google_access_token(acct)).encode()
        sent = []

        def answer(_challenge):
            if sent:                      # server replied with an error: send an empty line
                return b""
            sent.append(True)
            return auth
        M.authenticate("XOAUTH2", answer)
    else:
        M.login(acct.get("username") or acct["email"], get_password(acct))
    return M


def smtp_connect(acct):
    host, port = acct["smtp_host"], int(acct.get("smtp_port") or 587)
    sec = acct.get("smtp_security", "STARTTLS")
    ctx = ssl.create_default_context()
    if sec == "SSL/TLS":
        s = smtplib.SMTP_SSL(host, port, context=ctx, timeout=30)
    else:
        s = smtplib.SMTP(host, port, timeout=30)
        s.ehlo()
        if sec == "STARTTLS":
            s.starttls(context=ctx)
            s.ehlo()
    if acct.get("auth_type") == "oauth_google":
        auth = xoauth2_string(acct["email"], google_access_token(acct))
        s.auth("XOAUTH2", lambda challenge=None: "" if challenge else auth, initial_response_ok=True)
    elif acct.get("smtp_auth", True):
        s.login(acct.get("username") or acct["email"], get_password(acct))
    return s


def send_raw(acct, raw):
    """Send a stored message. Strips Bcc. Returns the bytes as sent."""
    m = parse_msg(raw)
    rcpts = [a for _, a in parse_addresses(hdr(m, "To"), hdr(m, "Cc"), hdr(m, "Bcc"))]
    if not rcpts:
        raise ValueError("The message has no recipients.")
    del m["Bcc"]
    out = m.as_bytes(policy=policy.SMTP)
    s = smtp_connect(acct)
    try:
        s.sendmail(acct["email"], rcpts, out)
    finally:
        try:
            s.quit()
        except Exception:
            pass
    return m.as_bytes()


class SyncWorker(QThread):
    progress = Signal(str)
    error = Signal(str)
    done = Signal(int)

    def __init__(self, accounts, db_path, fetch_limit=300, send=True, receive=True):
        super().__init__()
        self.accounts = [dict(a) for a in accounts]
        self.db_path = db_path
        self.fetch_limit = fetch_limit
        self.do_send = send
        self.do_receive = receive

    def run(self):
        st = Store(self.db_path)
        new = 0
        if self.do_send:
            rows = st.db.execute("SELECT id, account, raw FROM messages WHERE folder='Outbox'").fetchall()
            for i, row in enumerate(rows):
                acct = next((a for a in self.accounts if a["id"] == row["account"] and a.get("smtp_host")),
                            None) or next((a for a in self.accounts if a.get("smtp_host")), None)
                if not acct:
                    self.error.emit("No account is set up to send mail.")
                    break
                self.progress.emit(f"Sending message {i + 1} of {len(rows)} via '{acct['smtp_host']}'...")
                try:
                    sent = send_raw(acct, row["raw"])
                    st.db.execute("UPDATE messages SET folder='Sent Items', raw=?, is_read=1, ts=? "
                                  "WHERE id=?", (sent, time.time(), row["id"]))
                    st.db.commit()
                except Exception as e:
                    self.error.emit(f"Could not send '{summarize(row['raw'])['subject'] or '(no subject)'}' "
                                    f"from account '{acct.get('name')}': {friendly_error(e)}")
        if self.do_receive:
            for acct in self.accounts:
                if not acct.get("imap_host"):
                    continue
                try:
                    self.progress.emit(f"Connecting to '{acct['imap_host']}'...")
                    M = imap_connect(acct)
                    try:
                        self.progress.emit(f"Checking for new messages on '{acct.get('name')}'...")
                        M.select("INBOX", readonly=True)
                        uv = M.response("UIDVALIDITY")[1]
                        uv = (uv[0].decode() if uv and uv[0] else "0")
                        typ, data = M.uid("search", None, "ALL")
                        uids = data[0].split() if data and data[0] else []
                        uids = uids[-self.fetch_limit:]
                        known = st.known_remote(acct["id"])
                        todo = [u for u in uids if f"{uv}:{u.decode()}" not in known]
                        for i, u in enumerate(todo):
                            self.progress.emit(f"Receiving message {i + 1} of {len(todo)} "
                                               f"from '{acct.get('name')}'...")
                            typ, msgdata = M.uid("fetch", u, "(FLAGS BODY.PEEK[])")
                            raw = None
                            meta = b""
                            for part in msgdata or []:
                                if isinstance(part, tuple):
                                    meta += part[0]
                                    raw = part[1]
                                elif isinstance(part, bytes):
                                    meta += part
                            if raw:
                                if st.add_message("Inbox", raw, account=acct["id"],
                                                  remote_uid=f"{uv}:{u.decode()}",
                                                  is_read=int(b"\\Seen" in meta)):
                                    new += 1
                    finally:
                        try:
                            M.logout()
                        except Exception:
                            pass
                except Exception as e:
                    self.error.emit(f"Could not receive mail for '{acct.get('name')}' "
                                    f"({acct.get('imap_host')}): {friendly_error(e)}")
        st.db.close()
        self.done.emit(new)


# --------------------------------------------------------------------------
# Small reusable widgets
# --------------------------------------------------------------------------

class Panel(QWidget):
    """A pane with the OE-style header strip ('Folders  x')."""

    def __init__(self, title, content, on_close=None, menu=None):
        super().__init__()
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        head = QFrame()
        head.setObjectName("paneHeader")
        h = QHBoxLayout(head)
        h.setContentsMargins(5, 1, 1, 1)
        if menu:
            b = QToolButton()
            b.setText(title + "  ▾")
            b.setMenu(menu)
            b.setPopupMode(QToolButton.InstantPopup)
            b.setStyleSheet("QToolButton::menu-indicator { image: none; }")
            h.addWidget(b)
        else:
            h.addWidget(QLabel(title))
        h.addStretch()
        if on_close:
            x = QToolButton()
            x.setText("✕")
            x.setToolTip("Close")
            x.clicked.connect(on_close)
            h.addWidget(x)
        v.addWidget(head)
        v.addWidget(content)


class FolderDelegate(QStyledItemDelegate):
    """Draws 'Inbox (3)' with the count in bold blue, like OE."""

    def paint(self, painter, option, index):
        count = index.data(COUNT_ROLE) or 0
        opt = QStyleOptionViewItem(option)
        self.initStyleOption(opt, index)
        if count:
            f = QFont(opt.font)
            f.setBold(True)
            opt.font = f
        style = opt.widget.style() if opt.widget else QApplication.style()
        style.drawControl(QStyle.CE_ItemViewItem, opt, painter, opt.widget)
        if count:
            r = style.subElementRect(QStyle.SE_ItemViewItemText, opt, opt.widget)
            fm = QFontMetrics(opt.font)
            x = r.left() + fm.horizontalAdvance(opt.text) + 6
            painter.save()
            painter.setFont(opt.font)
            selected = bool(opt.state & QStyle.State_Selected)
            painter.setPen(QColor("#FFFFFF") if selected else QColor("#0000FF"))
            painter.drawText(QRect(x, r.top(), 80, r.height()), Qt.AlignVCenter | Qt.AlignLeft,
                             f"({count})")
            painter.restore()

    def sizeHint(self, option, index):
        s = super().sizeHint(option, index)
        if index.data(COUNT_ROLE):
            s.setWidth(s.width() + 44)
        return s


class MsgItem(QTreeWidgetItem):
    def __lt__(self, other):
        col = self.treeWidget().sortColumn() if self.treeWidget() else 0
        a, b = self.data(col, SORT_ROLE), other.data(col, SORT_ROLE)
        if a is not None and b is not None:
            return a < b
        return self.text(col).lower() < other.text(col).lower()


class MultiCompleter(QCompleter):
    """Completes the last address in a comma-separated list."""

    def splitPath(self, path):
        return [path.split(",")[-1].strip()]

    def pathFromIndex(self, index):
        text = super().pathFromIndex(index)
        parts = [p.strip() for p in self.widget().text().split(",")[:-1] if p.strip()]
        parts.append(text)
        return ", ".join(parts) + ", "


REMOTE_RE = re.compile(r"""(?:\b(?:src|background|poster|srcset)\s*=\s*["']?\s*(?:https?:)?//)"""
                       r"""|(?:url\(\s*["']?\s*(?:https?:)?//)""", re.I)
REMOTE_IMG_RE = re.compile(r"""<img\b[^>]*\bsrc\s*=\s*["']?\s*(?:https?:)?//[^>]*>""", re.I)
BLOCKED_TEXT = ("Some pictures have been blocked to help prevent the sender from identifying your "
                "computer. <a href='#'>Click here to download pictures.</a>")


def prepare_message_html(m, outdir):
    """Message HTML with inline (cid:) pictures saved next to it. Returns (html, has_remote)."""
    text = body_html(m)
    outdir.mkdir(parents=True, exist_ok=True)
    try:
        parts = list(m.walk())
    except Exception:
        parts = []
    for i, part in enumerate(parts):
        cid = (part.get("Content-ID") or "").strip().strip("<>")
        if not cid or part.is_multipart():
            continue
        data = part.get_payload(decode=True) or b""
        ext = mimetypes.guess_extension(part.get_content_type()) or ".bin"
        fname = f"inline{i}{ext}"
        (outdir / fname).write_bytes(data)
        text = re.sub(r"cid:<?" + re.escape(cid) + r">?", fname, text, flags=re.I)
    return text, bool(REMOTE_RE.search(text))


class MailBody(QWidget):
    """Shows a message body. Uses Chromium (QtWebEngine) when available: proper layout,
    scripts off, web pictures blocked until you click the yellow bar."""

    _counter = 0

    def __init__(self, main):
        super().__init__()
        self.main = main
        MailBody._counter += 1
        self.dir = APP_DIR / "temp" / f"view{MailBody._counter}"
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        self.bar = QFrame()
        self.bar.setStyleSheet("QFrame { background:#FFFFE1; border:1px solid #7F9DB9; border-top:none; }"
                               "QLabel { border:none; background:transparent; }")
        bl = QHBoxLayout(self.bar)
        bl.setContentsMargins(6, 3, 6, 3)
        pic = QLabel()
        pic.setPixmap(make_pixmap("app", 16))
        self.bar_text = QLabel(BLOCKED_TEXT)
        self.bar_text.setWordWrap(True)
        self.bar_text.linkActivated.connect(lambda _: self.show_pictures())
        bl.addWidget(pic, 0, Qt.AlignTop)
        bl.addWidget(self.bar_text, 1)
        self.bar.hide()
        v.addWidget(self.bar)
        self.current = None
        self.allow = False
        if HAVE_WEBENGINE:
            self.view = QWebEngineView()
            self.view.setStyleSheet("border:1px solid #7F9DB9;")
            self.profile = QWebEngineProfile(self)          # off-the-record: no cookies kept
            self.blocker = RemoteBlocker(self.profile)
            self.profile.setUrlRequestInterceptor(self.blocker)
            page = MailPage(self.profile, self.view, main)
            s = page.settings()
            s.setAttribute(QWebEngineSettings.JavascriptEnabled, False)
            s.setAttribute(QWebEngineSettings.PluginsEnabled, False)
            s.setAttribute(QWebEngineSettings.LocalContentCanAccessRemoteUrls, True)
            s.setAttribute(QWebEngineSettings.AutoLoadImages, True)
            self.view.setPage(page)
        else:
            self.view = QTextBrowser()
            self.view.setOpenExternalLinks(True)
            self.view.setStyleSheet("QTextBrowser { border-top: none; }")
        v.addWidget(self.view, 1)

    def clear(self):
        self.current = None
        self.bar.hide()
        if HAVE_WEBENGINE:
            self.view.setHtml("")
        else:
            self.view.setHtml("")

    def show_message(self, m, key=None):
        self.current = m
        self.allow = not self.main.cfg.get("block_images")
        self._render()

    def show_pictures(self):
        self.allow = True
        self._render()

    def _render(self):
        m = self.current
        if m is None:
            return
        try:
            shutil.rmtree(self.dir, ignore_errors=True)
        except Exception:
            pass
        text, has_remote = prepare_message_html(m, self.dir)
        self.bar.setVisible(has_remote and not self.allow)
        if HAVE_WEBENGINE:
            self.blocker.allow = self.allow
            path = self.dir / "message.html"
            # UTF-8 BOM wins over any charset the e-mail itself declares
            path.write_text(text, encoding="utf-8-sig")
            self.view.setUrl(QUrl.fromLocalFile(str(path)))
        else:
            if not self.allow:
                text = REMOTE_IMG_RE.sub("", text)
            self.view.document().setBaseUrl(QUrl.fromLocalFile(str(self.dir) + "/"))
            self.view.setHtml(text)


class PreviewPane(QWidget):
    """The preview pane: header strip (From/To/Subject) + message body."""

    def __init__(self, main):
        super().__init__()
        self.main = main
        self.atts = []
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        self.header = QFrame()
        self.header.setObjectName("previewHeader")
        g = QGridLayout(self.header)
        g.setContentsMargins(8, 4, 6, 4)
        g.setHorizontalSpacing(6)
        g.setVerticalSpacing(1)
        bold = QFont()
        bold.setBold(True)
        self.lbl = {}
        for row, key in enumerate(("From", "To", "Subject")):
            k = QLabel(key + ":")
            k.setFont(bold)
            val = QLabel()
            val.setTextInteractionFlags(Qt.TextSelectableByMouse)
            if key == "Subject":
                val.setFont(bold)
            g.addWidget(k, row, 0, Qt.AlignRight)
            g.addWidget(val, row, 1)
            self.lbl[key] = val
        self.date_lbl = QLabel()
        g.addWidget(self.date_lbl, 0, 2, Qt.AlignRight)
        self.att_btn = QToolButton()
        self.att_btn.setIcon(icon("attach"))
        self.att_btn.setIconSize(QSize(20, 20))
        self.att_btn.setToolTip("Attachments")
        self.att_btn.setPopupMode(QToolButton.InstantPopup)
        self.att_btn.setAutoRaise(True)
        g.addWidget(self.att_btn, 1, 2, 2, 1, Qt.AlignRight)
        g.setColumnStretch(1, 1)
        self.body = MailBody(main)
        v.addWidget(self.header)
        v.addWidget(self.body, 1)
        self.clear()

    def clear(self):
        for val in self.lbl.values():
            val.setText("")
        self.date_lbl.setText("")
        self.att_btn.hide()
        self.body.clear()

    def show_message(self, row):
        m = parse_msg(row["raw"])
        to = hdr(m, "To")
        cc = hdr(m, "Cc")
        self.lbl["From"].setText(hdr(m, "From"))
        self.lbl["To"].setText(to + (f"    Cc: {cc}" if cc else ""))
        self.lbl["Subject"].setText(hdr(m, "Subject"))
        self.date_lbl.setText(fmt_date(row["ts"]))
        self.body.show_message(m, row["id"])
        self.atts = attachments_of(m)
        if self.atts:
            menu = QMenu(self)
            for part in self.atts:
                name = part.get_filename() or "attachment"
                payload = part.get_payload(decode=True) or b""
                sub = menu.addMenu(icon("attach"), f"{name}  ({max(1, len(payload) // 1024)} KB)")
                sub.addAction("Open", lambda n=name, d=payload: self.main.open_attachment(n, d))
                sub.addAction("Save As...", lambda n=name, d=payload: self.main.save_attachment(n, d))
            menu.addSeparator()
            menu.addAction("Save Attachments...", lambda: self.main.save_all_attachments(self.atts))
            self.att_btn.setMenu(menu)
            self.att_btn.show()
        else:
            self.att_btn.hide()


class SyncDialog(QDialog):
    """The 'Send/Recv' progress window."""

    def __init__(self, parent):
        super().__init__(parent)
        xp_frame(self)
        self.setWindowTitle(APP_NAME)
        self.setWindowIcon(icon("sendrecv"))
        self.resize(460, 280)
        v = QVBoxLayout(self)
        top = QHBoxLayout()
        pic = QLabel()
        pic.setPixmap(make_pixmap("sendrecv", 32))
        top.addWidget(pic)
        self.status = QLabel("Preparing...")
        top.addWidget(self.status, 1)
        self.hide_btn = QPushButton("Hide")
        self.hide_btn.clicked.connect(self.hide)
        top.addWidget(self.hide_btn)
        v.addLayout(top)
        self.bar = QProgressBar()
        self.bar.setRange(0, 0)
        v.addWidget(self.bar)
        self.tabs = QTabWidget()
        self.tasks = QListWidget()
        self.errors = QListWidget()
        self.errors.setWordWrap(True)
        self.tabs.addTab(self.tasks, "Tasks")
        self.tabs.addTab(self.errors, "Errors")
        v.addWidget(self.tabs, 1)

    def set_status(self, text):
        self.status.setText(text)
        self.tasks.addItem(text)
        self.tasks.scrollToBottom()

    def add_error(self, text):
        self.errors.addItem(QListWidgetItem(icon("delete"), text))
        self.tabs.setCurrentWidget(self.errors)
        self.tabs.setTabText(1, f"Errors ({self.errors.count()})")

    def finish(self):
        self.bar.setRange(0, 1)
        self.bar.setValue(1)
        self.hide_btn.setText("Close")
        if self.errors.count():
            self.status.setText("Finished with errors.")
            self.show()
            self.raise_()
        else:
            self.status.setText("Done.")
            QTimer.singleShot(600, self.close)


# --------------------------------------------------------------------------
# Accounts, options, address book dialogs
# --------------------------------------------------------------------------

PRESETS = {
    "Gmail": ("imap.gmail.com", 993, True, "smtp.gmail.com", 587, "STARTTLS"),
    "Yahoo Mail": ("imap.mail.yahoo.com", 993, True, "smtp.mail.yahoo.com", 465, "SSL/TLS"),
    "iCloud Mail": ("imap.mail.me.com", 993, True, "smtp.mail.me.com", 587, "STARTTLS"),
    "AOL Mail": ("imap.aol.com", 993, True, "smtp.aol.com", 465, "SSL/TLS"),
    "Fastmail": ("imap.fastmail.com", 993, True, "smtp.fastmail.com", 465, "SSL/TLS"),
}


class GoogleSetupDialog(QDialog):
    """One-time setup: register Express Mail with Google so 'Sign in with Google' works."""

    def __init__(self, parent):
        super().__init__(parent)
        xp_frame(self)
        self.setWindowTitle("Set Up Google Sign-In")
        self.setWindowIcon(icon("app"))
        v = QVBoxLayout(self)
        steps = QLabel(f"""
<p><b>Google only lets registered programs use "Sign in with Google".</b> This is a one-time,
free setup (about 10 minutes) that registers {APP_NAME} under your own Google account.</p>
<ol>
<li>Open the <a href="{GOOGLE_CONSOLE_URL}">Google Cloud console</a> and sign in. Create a project
    (any name, e.g. <i>{APP_NAME}</i>) when asked.</li>
<li>Click <b>Get started</b> under Google Auth Platform. Enter an app name and your e-mail,
    choose <b>External</b>, and finish.</li>
<li>Go to <b>Audience</b>. Click <b>Publish app</b> and confirm. (If you leave it in <i>Testing</i>,
    add yourself as a test user, but Google will sign you out every 7 days.)</li>
<li>Go to <b>Clients</b> &gt; <b>Create client</b>. Choose <b>Desktop app</b>, give it a name,
    click <b>Create</b>, then <b>Download JSON</b>.</li>
<li>Click <b>Import JSON file...</b> below and pick the file you downloaded.</li>
</ol>
<p style="color:#444">When you sign in, Google will warn that it <i>hasn't verified this app</i>.
That's expected, because the app is yours: click <b>Advanced</b>, then <b>Go to {APP_NAME}</b>.</p>""")
        steps.setWordWrap(True)
        steps.setOpenExternalLinks(True)
        steps.setTextFormat(Qt.RichText)
        v.addWidget(steps)
        g = QGroupBox("Your OAuth client")
        f = QFormLayout(g)
        cur = google_client() or {}
        self.cid = QLineEdit(cur.get("client_id", ""))
        self.cid.setPlaceholderText("....apps.googleusercontent.com")
        self.secret = QLineEdit(cur.get("client_secret", ""))
        self.secret.setEchoMode(QLineEdit.Password)
        imp = QPushButton("Import JSON file...")
        imp.clicked.connect(self._import)
        f.addRow("", imp)
        f.addRow("Client ID:", self.cid)
        f.addRow("Client secret:", self.secret)
        v.addWidget(g)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._ok)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)
        self.resize(560, 560)

    def _import(self):
        path, _ = QFileDialog.getOpenFileName(self, "Import Google Client File",
                                              str(Path.home() / "Downloads"), "JSON (*.json)")
        if path:
            try:
                cid, sec = read_client_secret_json(path)
            except Exception as e:
                XPMsg.warning(self, APP_NAME, f"That file couldn't be read:\n\n{e}")
                return
            if not cid or not sec:
                XPMsg.warning(self, APP_NAME, "That file doesn't contain a client ID and secret. "
                                    "Make sure you downloaded the JSON for a Desktop app client.")
                return
            self.cid.setText(cid)
            self.secret.setText(sec)

    def _ok(self):
        if not self.cid.text().strip() or not self.secret.text().strip():
            XPMsg.warning(self, APP_NAME, "Please import the JSON file, or fill in both boxes.")
            return
        save_google_client(self.cid.text(), self.secret.text())
        self.accept()


class GoogleSignInDialog(QDialog):
    """'Waiting for you to sign in...' while the browser does its thing."""

    def __init__(self, parent, login):
        super().__init__(parent)
        xp_frame(self)
        self.login = login
        self.setWindowTitle("Sign in with Google")
        self.setWindowIcon(icon("app"))
        v = QVBoxLayout(self)
        top = QHBoxLayout()
        pic = QLabel()
        pic.setPixmap(make_pixmap("app", 32))
        top.addWidget(pic)
        msg = QLabel("A browser window has opened.<br><b>Sign in with your Google account there</b>, "
                     f"then come back to {APP_NAME}.")
        msg.setWordWrap(True)
        top.addWidget(msg, 1)
        v.addLayout(top)
        bar = QProgressBar()
        bar.setRange(0, 0)
        v.addWidget(bar)
        row = QHBoxLayout()
        again = QPushButton("Open the page again")
        again.clicked.connect(login.open_browser)
        cancel = QPushButton("Cancel")
        cancel.clicked.connect(self.reject)
        row.addWidget(again)
        row.addStretch()
        row.addWidget(cancel)
        v.addLayout(row)
        self.resize(420, 140)
        self.timer = QTimer(self)
        self.timer.timeout.connect(self._poll)
        self.timer.start(200)

    def _poll(self):
        if self.login.done():
            self.timer.stop()
            self.accept()

    def reject(self):
        self.login.cancelled = True
        self.timer.stop()
        super().reject()


class AccountDialog(QDialog):
    def __init__(self, parent, acct=None):
        super().__init__(parent)
        xp_frame(self)
        self.acct = dict(acct) if acct else {"id": uuid.uuid4().hex}
        self.auth_type = self.acct.get("auth_type", "password")
        self.new_refresh_token = None
        self.setWindowTitle(f"{acct.get('name', 'Mail')} Properties" if acct else "Add Mail Account")
        self.setWindowIcon(icon("app"))
        v = QVBoxLayout(self)
        tabs = QTabWidget()
        v.addWidget(tabs)

        gen = QWidget()
        f = QFormLayout(gen)
        self.preset = QComboBox()
        self.preset.addItems(["Other (IMAP)"] + list(PRESETS))
        self.preset.currentTextChanged.connect(self._apply_preset)
        self.name = QLineEdit(self.acct.get("name", ""))
        self.display = QLineEdit(self.acct.get("display", ""))
        self.email = QLineEdit(self.acct.get("email", ""))
        self.default = QCheckBox("Use this as my default mail account")
        self.default.setChecked(bool(self.acct.get("default")))
        f.addRow("Mail provider:", self.preset)
        self.google_box = QFrame()
        self.google_box.setStyleSheet("QFrame#gbox { background:#FFFFFF; border:1px solid #7F9DB9; }")
        self.google_box.setObjectName("gbox")
        gb = QVBoxLayout(self.google_box)
        self.google_btn = QPushButton("  Sign in with Google...")
        self.google_btn.setIcon(icon("app"))
        self.google_btn.setDefault(False)
        self.google_btn.setAutoDefault(False)
        self.google_btn.clicked.connect(self._google_sign_in)
        self.google_status = QLabel()
        self.google_status.setWordWrap(True)
        self.google_status.setStyleSheet("border:none; background:transparent;")
        self.use_pw_btn = QPushButton("Use an app password instead")
        self.use_pw_btn.setAutoDefault(False)
        self.use_pw_btn.clicked.connect(self._use_password)
        gb.addWidget(self.google_btn)
        gb.addWidget(self.google_status)
        gb.addWidget(self.use_pw_btn, 0, Qt.AlignLeft)
        f.addRow("", self.google_box)
        f.addRow("Account name:", self.name)
        f.addRow("Your name:", self.display)
        f.addRow("E-mail address:", self.email)
        f.addRow("", self.default)
        tabs.addTab(gen, "General")

        srv = QWidget()
        sv = QVBoxLayout(srv)
        g1 = QGroupBox("Incoming mail (IMAP)")
        f1 = QFormLayout(g1)
        self.imap_host = QLineEdit(self.acct.get("imap_host", ""))
        self.imap_port = QSpinBox()
        self.imap_port.setRange(1, 65535)
        self.imap_port.setValue(int(self.acct.get("imap_port", 993)))
        self.imap_ssl = QCheckBox("This server requires a secure connection (SSL)")
        self.imap_ssl.setChecked(self.acct.get("imap_ssl", True))
        f1.addRow("Server:", self.imap_host)
        f1.addRow("Port:", self.imap_port)
        f1.addRow("", self.imap_ssl)
        g2 = QGroupBox("Outgoing mail (SMTP)")
        f2 = QFormLayout(g2)
        self.smtp_host = QLineEdit(self.acct.get("smtp_host", ""))
        self.smtp_port = QSpinBox()
        self.smtp_port.setRange(1, 65535)
        self.smtp_port.setValue(int(self.acct.get("smtp_port", 587)))
        self.smtp_sec = QComboBox()
        self.smtp_sec.addItems(["STARTTLS", "SSL/TLS", "None"])
        self.smtp_sec.setCurrentText(self.acct.get("smtp_security", "STARTTLS"))
        self.smtp_auth = QCheckBox("My server requires authentication")
        self.smtp_auth.setChecked(self.acct.get("smtp_auth", True))
        f2.addRow("Server:", self.smtp_host)
        f2.addRow("Port:", self.smtp_port)
        f2.addRow("Security:", self.smtp_sec)
        f2.addRow("", self.smtp_auth)
        g3 = QGroupBox("Logon")
        f3 = QFormLayout(g3)
        self.username = QLineEdit(self.acct.get("username", ""))
        self.username.setPlaceholderText("Usually your full e-mail address")
        self.password = QLineEdit(get_password(self.acct) if acct and self.auth_type == "password" else "")
        self.password.setEchoMode(QLineEdit.Password)
        f3.addRow("Account name:", self.username)
        f3.addRow("Password:", self.password)
        sv.addWidget(g1)
        sv.addWidget(g2)
        sv.addWidget(g3)
        tabs.addTab(srv, "Servers")

        note = QLabel("Gmail: use <b>Sign in with Google</b>. Yahoo and iCloud need an <b>app password</b> "
                      "(made in your account's security settings).<br>Outlook.com/Hotmail aren't "
                      "supported yet.")
        note.setWordWrap(True)
        note.setStyleSheet("color:#444444; padding:4px;")
        v.addWidget(note)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        test = bb.addButton("Test Settings", QDialogButtonBox.ActionRole)
        test.clicked.connect(self._test)
        bb.accepted.connect(self._accept)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)
        self.resize(460, 560)
        if self.acct.get("imap_host") == "imap.gmail.com":
            self.preset.blockSignals(True)
            self.preset.setCurrentText("Gmail")
            self.preset.blockSignals(False)
        elif not acct:
            self.preset.setCurrentText("Gmail")
        self._update_google_ui()

    # ---- Google sign-in
    def _signed_in(self):
        return self.auth_type == "oauth_google" and (self.new_refresh_token or get_password(self.acct))

    def _update_google_ui(self):
        is_gmail = self.preset.currentText() == "Gmail" or self.auth_type == "oauth_google"
        self.google_box.setVisible(is_gmail)
        oauth = self.auth_type == "oauth_google"
        if oauth and self._signed_in():
            self.google_status.setText(f"✔ Signed in as <b>{html.escape(self.email.text())}</b>. "
                                       "No password needed.")
            self.google_btn.setText("  Sign in again / switch account...")
        else:
            self.google_status.setText("The easy way: sign in with your Google account in your browser. "
                                       "No app password needed.")
            self.google_btn.setText("  Sign in with Google...")
        self.use_pw_btn.setVisible(oauth)
        self.password.setEnabled(not oauth)
        self.password.setPlaceholderText("Signed in with Google - not needed" if oauth else "")
        self.smtp_auth.setEnabled(not oauth)

    def _use_password(self):
        self.auth_type = "password"
        self.new_refresh_token = None
        self._update_google_ui()

    def _google_sign_in(self):
        client = google_client()
        if not client:
            if not GoogleSetupDialog(self).exec():
                return
            client = google_client()
        try:
            login = GoogleLogin(client, login_hint=self.email.text().strip())
        except Exception as e:
            XPMsg.warning(self, APP_NAME, f"Couldn't start Google sign-in:\n\n{e}")
            return
        login.start()
        if not GoogleSignInDialog(self, login).exec():
            return
        self.raise_()
        self.activateWindow()
        if login.error:
            msg = {"access_denied": "Sign-in was cancelled, or Google didn't allow it.\n\nIf your Google "
                                    "app is still in 'Testing', make sure your address is listed as a "
                                    "test user (Google Cloud console > Audience)."}
            XPMsg.warning(self, APP_NAME, msg.get(login.error, f"Google sign-in failed: {login.error}"))
            return
        QApplication.setOverrideCursor(Qt.WaitCursor)
        try:
            tokens = login.exchange()
        except Exception as e:
            QApplication.restoreOverrideCursor()
            hint = ("\n\nThe client ID or secret looks wrong. Choose 'Set up again' to re-import it."
                    if isinstance(e, OAuthError) and e.code in ("invalid_client", "unauthorized_client") else "")
            if XPMsg.warning(self, APP_NAME, f"Google sign-in failed:\n\n{e}{hint}",
                                   QMessageBox.Retry | QMessageBox.Cancel) == QMessageBox.Retry:
                GoogleSetupDialog(self).exec()
            return
        QApplication.restoreOverrideCursor()
        if not tokens.get("refresh_token"):
            XPMsg.warning(self, APP_NAME, "Google didn't return a long-term sign-in. Please try again.")
            return
        claims = jwt_claims(tokens.get("id_token", ""))
        if claims.get("email"):
            self.email.setText(claims["email"])
            self.username.setText(claims["email"])
        if claims.get("name") and not self.display.text().strip():
            self.display.setText(claims["name"])
        if not self.name.text().strip():
            self.name.setText("Gmail")
        self._apply_preset("Gmail")
        self.auth_type = "oauth_google"
        self.new_refresh_token = tokens["refresh_token"]
        remember_access_token(self.acct["id"], tokens["access_token"], tokens.get("expires_in"))
        self._update_google_ui()

    def _apply_preset(self, name):
        if hasattr(self, "google_box"):
            self._update_google_ui()
        if name in PRESETS:
            ih, ip, issl, sh, sp, ssec = PRESETS[name]
            self.imap_host.setText(ih)
            self.imap_port.setValue(ip)
            self.imap_ssl.setChecked(issl)
            self.smtp_host.setText(sh)
            self.smtp_port.setValue(sp)
            self.smtp_sec.setCurrentText(ssec)
            if not self.name.text():
                self.name.setText(name)

    def _collect(self):
        a = self.acct
        a.update(name=self.name.text().strip() or self.email.text().strip() or "Mail",
                 display=self.display.text().strip(), email=self.email.text().strip(),
                 imap_host=self.imap_host.text().strip(), imap_port=self.imap_port.value(),
                 imap_ssl=self.imap_ssl.isChecked(), smtp_host=self.smtp_host.text().strip(),
                 smtp_port=self.smtp_port.value(), smtp_security=self.smtp_sec.currentText(),
                 smtp_auth=self.smtp_auth.isChecked(),
                 username=self.username.text().strip() or self.email.text().strip(),
                 default=self.default.isChecked(), auth_type=self.auth_type)
        if self.auth_type == "oauth_google":
            a["smtp_auth"] = True
            if self.new_refresh_token:
                set_password(a, self.new_refresh_token)   # the refresh token, kept in Credential Manager
        else:
            set_password(a, self.password.text())
            with _TOKEN_LOCK:
                _TOKEN_CACHE.pop(a["id"], None)
        return a

    def _test(self):
        a = self._collect()
        QApplication.setOverrideCursor(Qt.WaitCursor)
        results = []
        try:
            M = imap_connect(a)
            M.logout()
            results.append("✔  Logged on to the incoming mail server.")
        except Exception as e:
            results.append(f"✘  Incoming mail server: {friendly_error(e)}")
        try:
            s = smtp_connect(a)
            s.quit()
            results.append("✔  Logged on to the outgoing mail server.")
        except Exception as e:
            results.append(f"✘  Outgoing mail server: {friendly_error(e)}")
        QApplication.restoreOverrideCursor()
        XPMsg.information(self, "Test Account Settings", "\n\n".join(results))

    def _accept(self):
        if "@" not in self.email.text():
            XPMsg.warning(self, APP_NAME, "Please enter a valid e-mail address, "
                                "or click 'Sign in with Google'.")
            return
        if self.auth_type == "oauth_google" and not self._signed_in():
            XPMsg.warning(self, APP_NAME, "Please finish 'Sign in with Google' first.")
            return
        self._collect()
        self.accept()


class AccountsDialog(QDialog):
    def __init__(self, main):
        super().__init__(main)
        xp_frame(self)
        self.main = main
        self.cfg = main.cfg
        self.setWindowTitle("Internet Accounts")
        self.setWindowIcon(icon("app"))
        self.resize(480, 300)
        h = QHBoxLayout(self)
        tabs = QTabWidget()
        page = QWidget()
        pv = QVBoxLayout(page)
        self.list = QListWidget()
        self.list.itemDoubleClicked.connect(lambda *_: self.edit())
        pv.addWidget(self.list)
        tabs.addTab(page, "Mail")
        h.addWidget(tabs, 1)
        col = QVBoxLayout()
        for text, slot in (("Add...", self.add), ("Remove", self.remove),
                           ("Properties", self.edit), ("Set as Default", self.make_default)):
            b = QPushButton(text)
            b.clicked.connect(slot)
            col.addWidget(b)
        col.addStretch()
        close = QPushButton("Close")
        close.clicked.connect(self.accept)
        col.addWidget(close)
        h.addLayout(col)
        self.refresh()

    def refresh(self):
        self.list.clear()
        for a in self.cfg.accounts:
            text = f"{a.get('name')}   -   {a.get('email')}" + ("   (default)" if a.get("default") else "")
            it = QListWidgetItem(icon("app"), text)
            it.setData(Qt.UserRole, a["id"])
            self.list.addItem(it)

    def _current(self):
        it = self.list.currentItem()
        return self.cfg.account(it.data(Qt.UserRole)) if it else None

    def add(self):
        d = AccountDialog(self)
        if d.exec():
            if not self.cfg.accounts:
                d.acct["default"] = True
            if d.acct.get("default"):
                for a in self.cfg.accounts:
                    a["default"] = False
            self.cfg.accounts.append(d.acct)
            self.cfg.save()
            self.refresh()
            self.main.accounts_changed()

    def edit(self):
        a = self._current()
        if not a:
            return
        d = AccountDialog(self, a)
        if d.exec():
            if d.acct.get("default"):
                for other in self.cfg.accounts:
                    other["default"] = False
            a.clear()
            a.update(d.acct)
            self.cfg.save()
            self.refresh()
            self.main.accounts_changed()

    def remove(self):
        a = self._current()
        if a and XPMsg.question(self, APP_NAME, f"Remove the account '{a.get('name')}'?\n\n"
                                      "Messages already downloaded stay in your folders.") == QMessageBox.Yes:
            if keyring and a.get("pw_in_keyring"):
                try:
                    keyring.delete_password("ExpressMail", a["id"])
                except Exception:
                    pass
            self.cfg.accounts.remove(a)
            self.cfg.save()
            self.refresh()
            self.main.accounts_changed()

    def make_default(self):
        a = self._current()
        if a:
            for other in self.cfg.accounts:
                other["default"] = other is a
            self.cfg.save()
            self.refresh()


def theme_preview(name, w=230, h=30):
    """A small picture of a title bar in the given color scheme."""
    T = THEMES[name]
    pm = QPixmap(w, h)
    pm.fill(QColor(T["face"]))
    p = QPainter(pm)
    p.setRenderHint(QPainter.Antialiasing)
    g = QLinearGradient(0, 0, 0, 24)
    for pos, col in T["title_active"]:
        g.setColorAt(pos, QColor(col))
    p.fillRect(0, 0, w, 24, QBrush(g))
    for i, c in enumerate(T["edge_lt"][:3]):
        p.fillRect(i, 24, 1, h - 24, QColor(c))
        p.fillRect(w - 1 - i, 24, 1, h - 24, QColor(T["edge_rb"][i]))
    icon("app").paint(p, QRect(5, 4, 16, 16))
    f = QFont("Trebuchet MS")
    f.setBold(True)
    f.setPixelSize(12)
    p.setFont(f)
    p.setPen(QColor(T["title_shadow"]))
    p.drawText(QRect(26, 1, 120, 24), Qt.AlignVCenter, APP_NAME)
    p.setPen(QColor(T["title_text"]))
    p.drawText(QRect(25, 0, 120, 24), Qt.AlignVCenter, APP_NAME)
    x = w - 4 - 18
    for kind in ("close", "max", "min"):
        c0, c1 = T["close"] if kind == "close" else T["cap"]
        gg = QLinearGradient(x, 3, x + 18, 21)
        gg.setColorAt(0, QColor(c0))
        gg.setColorAt(1, QColor(c1))
        p.setPen(QPen(QColor(T["cap_border"]), 1))
        p.setBrush(QBrush(gg))
        p.drawRoundedRect(QRectF(x + 0.5, 3.5, 17, 17), 3, 3)
        glyph = QColor("#FFFFFF" if kind == "close" else T["cap_glyph"])
        if kind == "close":
            p.setPen(_pen(glyph.name(), 2))
            p.drawLine(QPointF(x + 5.5, 8.5), QPointF(x + 12.5, 15.5))
            p.drawLine(QPointF(x + 12.5, 8.5), QPointF(x + 5.5, 15.5))
        elif kind == "max":
            p.setPen(QPen(glyph, 1))
            p.setBrush(Qt.NoBrush)
            p.drawRect(QRectF(x + 4.5, 7.5, 9, 8))
            p.fillRect(QRectF(x + 4, 7, 10, 2.5), glyph)
        else:
            p.fillRect(QRectF(x + 4, 14, 6, 2.5), glyph)
        x -= 20
    p.end()
    return pm


class OptionsDialog(QDialog):
    def __init__(self, main):
        super().__init__(main)
        xp_frame(self)
        self.cfg = main.cfg
        self.setWindowTitle("Options")
        self.setWindowIcon(icon("app"))
        v = QVBoxLayout(self)
        tabs = QTabWidget()
        v.addWidget(tabs)
        gen = QWidget()
        gv = QVBoxLayout(gen)
        g = QGroupBox("Send / Receive Messages")
        gl = QGridLayout(g)
        self.sound = QCheckBox("Play sound when new messages arrive")
        self.sound.setChecked(self.cfg.get("play_sound"))
        self.check = QCheckBox("Check for new messages every")
        self.check.setChecked(self.cfg.get("check_enabled"))
        self.minutes = QSpinBox()
        self.minutes.setRange(1, 480)
        self.minutes.setValue(self.cfg.get("check_minutes"))
        gl.addWidget(self.sound, 0, 0, 1, 3)
        gl.addWidget(self.check, 1, 0)
        gl.addWidget(self.minutes, 1, 1)
        gl.addWidget(QLabel("minute(s)"), 1, 2)
        self.limit = QSpinBox()
        self.limit.setRange(10, 100000)
        self.limit.setValue(self.cfg.get("fetch_limit"))
        gl.addWidget(QLabel("Download at most the newest"), 2, 0)
        gl.addWidget(self.limit, 2, 1)
        gl.addWidget(QLabel("messages"), 2, 2)
        self.start_inbox = QCheckBox(f"When {APP_NAME} starts, go directly to my 'Inbox' folder")
        self.start_inbox.setChecked(self.cfg.get("start_in_inbox"))
        gv.addWidget(self.start_inbox)
        gv.addWidget(g)
        gv.addStretch()
        tabs.addTab(gen, "General")
        rd = QWidget()
        rl = QGridLayout(rd)
        rl.addWidget(QLabel("Mark message read after displaying for"), 0, 0)
        self.delay = QSpinBox()
        self.delay.setRange(0, 60)
        self.delay.setValue(self.cfg.get("read_delay"))
        rl.addWidget(self.delay, 0, 1)
        rl.addWidget(QLabel("second(s)"), 0, 2)
        rl.setRowStretch(1, 1)
        tabs.addTab(rd, "Read")
        sd = QWidget()
        sl = QVBoxLayout(sd)
        self.immediate = QCheckBox("Send messages immediately")
        self.immediate.setChecked(self.cfg.get("send_immediately"))
        sl.addWidget(self.immediate)
        sl.addStretch()
        tabs.addTab(sd, "Send")
        sec = QWidget()
        secl = QVBoxLayout(sec)
        g = QGroupBox("Download Images")
        gl2 = QVBoxLayout(g)
        self.block = QCheckBox("Block images and other external content in HTML e-mail")
        self.block.setChecked(self.cfg.get("block_images"))
        gl2.addWidget(self.block)
        secl.addWidget(g)
        secl.addStretch()
        tabs.addTab(sec, "Security")

        # ---- Appearance
        ap = QWidget()
        al = QVBoxLayout(ap)
        g3 = QGroupBox("Color scheme")
        gl3 = QVBoxLayout(g3)
        self.theme_group = QButtonGroup(self)
        current = self.cfg.get("theme") if self.cfg.get("theme") in THEMES else "Blue"
        for key, t in THEMES.items():
            row = QHBoxLayout()
            rb = QRadioButton(t["label"])
            rb.setMinimumWidth(120)
            rb.setChecked(key == current)
            rb.setProperty("theme", key)
            self.theme_group.addButton(rb)
            pic = QLabel()
            pic.setPixmap(theme_preview(key))
            pic.setCursor(Qt.PointingHandCursor)
            pic.mousePressEvent = lambda _e, b=rb: b.setChecked(True)
            row.addWidget(rb)
            row.addWidget(pic)
            row.addStretch()
            gl3.addLayout(row)
        al.addWidget(g3)
        self.xp_bars = QCheckBox("Use Windows XP title bars (takes effect next time you start)")
        self.xp_bars.setChecked(self.cfg.get("xp_titlebars"))
        al.addWidget(self.xp_bars)
        al.addStretch()
        tabs.addTab(ap, "Appearance")
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self._save)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)
        self.resize(430, 300)

    def _save(self):
        c = self.cfg
        c.set("play_sound", self.sound.isChecked())
        c.set("check_enabled", self.check.isChecked())
        c.set("check_minutes", self.minutes.value())
        c.set("fetch_limit", self.limit.value())
        c.set("start_in_inbox", self.start_inbox.isChecked())
        c.set("xp_titlebars", self.xp_bars.isChecked())
        chosen = self.theme_group.checkedButton()
        if chosen is not None:
            c.set("theme", chosen.property("theme"))
        c.set("read_delay", self.delay.value())
        c.set("send_immediately", self.immediate.isChecked())
        c.set("block_images", self.block.isChecked())
        c.save()
        self.accept()


class ContactDialog(QDialog):
    def __init__(self, parent, row=None, name="", email=""):
        super().__init__(parent)
        xp_frame(self)
        self.setWindowTitle(f"{row['name']} Properties" if row else "New Contact")
        self.setWindowIcon(icon("contact"))
        f = QFormLayout(self)
        self.name = QLineEdit(row["name"] if row else name)
        self.email = QLineEdit(row["email"] if row else email)
        self.phone = QLineEdit(row["phone"] if row else "")
        self.notes = QTextEdit(row["notes"] if row else "")
        self.notes.setAcceptRichText(False)
        self.notes.setFixedHeight(80)
        f.addRow("Display:", self.name)
        f.addRow("E-Mail:", self.email)
        f.addRow("Phone:", self.phone)
        f.addRow("Notes:", self.notes)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        f.addRow(bb)
        self.resize(360, 240)

    def values(self):
        return (self.name.text().strip() or self.email.text().strip(), self.email.text().strip(),
                self.phone.text().strip(), self.notes.toPlainText())


class AddressBook(QMainWindow):
    def __init__(self, main):
        super().__init__(main)
        xp_frame(self)
        self.main = main
        self.store = main.store
        self.setWindowTitle("Address Book - Main Identity")
        self.setWindowIcon(icon("addresses"))
        tb = QToolBar()
        tb.setMovable(False)
        tb.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        tb.setIconSize(QSize(24, 24))
        self.addToolBar(tb)
        for text, ic, slot in (("New", "contact", self.new), ("Properties", "drafts", self.edit),
                               ("Delete", "delete", self.delete), ("Action", "new", self.mail)):
            a = tb.addAction(icon(ic), text)
            a.triggered.connect(slot)
        w = QWidget()
        v = QVBoxLayout(w)
        v.setContentsMargins(4, 4, 4, 4)
        row = QHBoxLayout()
        row.addWidget(QLabel("Type name or select from list:"))
        self.filter = QLineEdit()
        self.filter.textChanged.connect(self.refresh)
        row.addWidget(self.filter, 1)
        v.addLayout(row)
        self.table = QTableWidget(0, 3)
        self.table.setHorizontalHeaderLabels(["Name", "E-Mail Address", "Phone"])
        self.table.horizontalHeader().setStretchLastSection(True)
        self.table.verticalHeader().hide()
        self.table.setSelectionBehavior(QAbstractItemView.SelectRows)
        self.table.setEditTriggers(QAbstractItemView.NoEditTriggers)
        self.table.setShowGrid(False)
        self.table.setColumnWidth(0, 180)
        self.table.setColumnWidth(1, 220)
        self.table.doubleClicked.connect(lambda *_: self.edit())
        v.addWidget(self.table)
        self.setCentralWidget(w)
        self.statusBar().showMessage("")
        self.resize(620, 400)
        self.refresh()

    def refresh(self):
        term = self.filter.text().lower()
        rows = [r for r in self.store.contacts()
                if term in (r["name"] or "").lower() or term in (r["email"] or "").lower()]
        self.table.setRowCount(len(rows))
        for i, r in enumerate(rows):
            it = QTableWidgetItem(icon("contact"), r["name"] or "")
            it.setData(Qt.UserRole, r["id"])
            self.table.setItem(i, 0, it)
            self.table.setItem(i, 1, QTableWidgetItem(r["email"] or ""))
            self.table.setItem(i, 2, QTableWidgetItem(r["phone"] or ""))
        self.statusBar().showMessage(f"{len(rows)} item(s)")

    def _cid(self):
        r = self.table.currentRow()
        return self.table.item(r, 0).data(Qt.UserRole) if r >= 0 and self.table.item(r, 0) else None

    def new(self):
        d = ContactDialog(self)
        if d.exec():
            self.store.save_contact(None, *d.values())
            self.refresh()
            self.main.refresh_contacts()

    def edit(self):
        cid = self._cid()
        row = next((r for r in self.store.contacts() if r["id"] == cid), None)
        if row:
            d = ContactDialog(self, row)
            if d.exec():
                self.store.save_contact(cid, *d.values())
                self.refresh()
                self.main.refresh_contacts()

    def delete(self):
        cid = self._cid()
        if cid and XPMsg.question(self, "Address Book",
                                        "Delete the selected contact?") == QMessageBox.Yes:
            self.store.delete_contact(cid)
            self.refresh()
            self.main.refresh_contacts()

    def mail(self):
        r = self.table.currentRow()
        if r >= 0:
            self.main.compose(to=formataddr((self.table.item(r, 0).text(), self.table.item(r, 1).text())))


class SelectRecipients(QDialog):
    def __init__(self, parent, store):
        super().__init__(parent)
        xp_frame(self)
        self.setWindowTitle("Select Recipients")
        self.setWindowIcon(icon("addresses"))
        v = QVBoxLayout(self)
        v.addWidget(QLabel("Select the people to add:"))
        self.list = QListWidget()
        self.list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        for r in store.contacts():
            it = QListWidgetItem(icon("contact"), f"{r['name']}  <{r['email']}>")
            it.setData(Qt.UserRole, formataddr((r["name"] or "", r["email"] or "")))
            self.list.addItem(it)
        self.list.itemDoubleClicked.connect(lambda *_: self.accept())
        v.addWidget(self.list)
        bb = QDialogButtonBox(QDialogButtonBox.Ok | QDialogButtonBox.Cancel)
        bb.accepted.connect(self.accept)
        bb.rejected.connect(self.reject)
        v.addWidget(bb)
        self.resize(360, 360)

    def chosen(self):
        return [it.data(Qt.UserRole) for it in self.list.selectedItems()]


# --------------------------------------------------------------------------
# Compose ("New Message") window
# --------------------------------------------------------------------------

class ComposeWindow(QMainWindow):
    def __init__(self, main, to="", cc="", bcc="", subject="", html_body="", attachments=None,
                 extra_headers=None, draft_id=None, account_id=None, priority=3):
        super().__init__()
        xp_frame(self)
        self.setAttribute(Qt.WA_DeleteOnClose)
        self.main = main
        self.store = main.store
        self.cfg = main.cfg
        self.attachments = list(attachments or [])
        self.extra_headers = extra_headers or {}
        self.draft_id = draft_id
        self.priority = priority
        self.dirty = False
        self.finished = False
        self.setWindowIcon(icon("new"))
        self.resize(720, 560)

        self._build_toolbar()
        self._build_menus()

        w = QWidget()
        v = QVBoxLayout(w)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)
        head = QFrame()
        head.setObjectName("composeHead")
        g = QGridLayout(head)
        g.setContentsMargins(6, 6, 6, 4)
        g.setVerticalSpacing(3)
        self.from_box = QComboBox()
        for a in self.cfg.accounts:
            self.from_box.addItem(f"{a.get('email')}   ({a.get('name')})", a["id"])
        acct = self.cfg.account(account_id) or self.cfg.default_account()
        if acct:
            self.from_box.setCurrentIndex(max(0, self.from_box.findData(acct["id"])))
        g.addWidget(QLabel("From:"), 0, 0, Qt.AlignRight)
        g.addWidget(self.from_box, 0, 1)
        if len(self.cfg.accounts) < 2:
            self.from_box.setEnabled(len(self.cfg.accounts) == 1)
        names = [formataddr((r["name"] or "", r["email"] or "")) for r in self.store.contacts()]
        self.fields = {}
        for row, (key, val) in enumerate((("To", to), ("Cc", cc), ("Bcc", bcc)), start=1):
            btn = QPushButton(icon("addresses"), f"{key}:")
            btn.setObjectName("addrButton")
            btn.setFocusPolicy(Qt.NoFocus)
            edit = QLineEdit(val)
            comp = MultiCompleter(names, edit)
            comp.setCaseSensitivity(Qt.CaseInsensitive)
            comp.setFilterMode(Qt.MatchContains)
            edit.setCompleter(comp)
            edit.textEdited.connect(self._touch)
            btn.clicked.connect(lambda _=False, e=edit: self._pick(e))
            g.addWidget(btn, row, 0)
            g.addWidget(edit, row, 1)
            self.fields[key] = (btn, edit)
        self.subject = QLineEdit(subject)
        self.subject.textChanged.connect(self._title)
        self.subject.textEdited.connect(self._touch)
        g.addWidget(QLabel("Subject:"), 4, 0, Qt.AlignRight)
        g.addWidget(self.subject, 4, 1)
        self.att_label = QLabel("Attach:")
        self.att_list = QListWidget()
        self.att_list.setFlow(QListView.LeftToRight)
        self.att_list.setFixedHeight(28)
        self.att_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.att_list.customContextMenuRequested.connect(self._att_menu)
        g.addWidget(self.att_label, 5, 0, Qt.AlignRight)
        g.addWidget(self.att_list, 5, 1)
        g.setColumnStretch(1, 1)
        v.addWidget(head)

        self.fmt = self._build_format_bar()
        v.addWidget(self.fmt)
        self.editor = QTextEdit()
        self.editor.document().setDefaultFont(QFont("Arial", 10))
        if html_body:
            self.editor.setHtml(html_body)
        self.editor.currentCharFormatChanged.connect(self._sync_format)
        self.editor.document().setModified(False)
        v.addWidget(self.editor, 1)
        self.setCentralWidget(w)

        show_bcc = bool(bcc)
        self.act_bcc.setChecked(show_bcc)
        self._show_bcc(show_bcc)
        self._refresh_atts()
        self._title()
        self.statusBar().showMessage("")
        if to:
            self.editor.setFocus()
            c = self.editor.textCursor()
            c.movePosition(QTextCursor.Start)
            self.editor.setTextCursor(c)
        else:
            self.fields["To"][1].setFocus()

    # -- construction
    def _act(self, text, ic, slot, shortcut=None, icon_text=None):
        a = QAction(icon(ic) if ic else QIcon(), text, self)
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
        if icon_text:
            a.setIconText(icon_text)
        a.triggered.connect(lambda _=False: slot())
        return a

    def _build_toolbar(self):
        tb = QToolBar("Standard")
        tb.setMovable(False)
        tb.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        tb.setIconSize(QSize(24, 24))
        self.addToolBar(tb)
        self.a_send = self._act("&Send Message", "send", self.send, "Alt+S", "Send")
        tb.addAction(self.a_send)
        tb.addSeparator()
        ed = lambda name: (lambda: getattr(self._focused_edit(), name)())
        self.a_cut = self._act("Cu&t", "cut", ed("cut"), None, "Cut")
        self.a_copy = self._act("&Copy", "copy", ed("copy"), None, "Copy")
        self.a_paste = self._act("&Paste", "paste", ed("paste"), None, "Paste")
        self.a_undo = self._act("&Undo", "undo", ed("undo"), None, "Undo")
        for a in (self.a_cut, self.a_copy, self.a_paste, self.a_undo):
            tb.addAction(a)
        tb.addSeparator()
        self.a_attach = self._act("File &Attachment...", "attach", self.add_attachment, None, "Attach")
        tb.addAction(self.a_attach)
        pm = QMenu(self)
        self.pri_actions = {}
        for val, label, ic in ((1, "High Priority", "high"), (3, "Normal Priority", None),
                               (5, "Low Priority", "low")):
            a = pm.addAction(icon(ic) if ic else QIcon(), label)
            a.setCheckable(True)
            a.triggered.connect(lambda _=False, v=val: self._set_priority(v))
            self.pri_actions[val] = a
        self.pri_btn = QToolButton()
        self.pri_btn.setText("Priority")
        self.pri_btn.setIcon(icon("high"))
        self.pri_btn.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        self.pri_btn.setMenu(pm)
        self.pri_btn.setPopupMode(QToolButton.InstantPopup)
        tb.addWidget(self.pri_btn)
        self._set_priority(self.priority, touch=False)

    def _build_menus(self):
        mb = self.menuBar()
        f = mb.addMenu("&File")
        f.addAction(self.a_send)
        f.addAction(self._act("&Save", "save", self.save_draft, "Ctrl+S"))
        f.addSeparator()
        f.addAction(self._act("&Close", None, self.close, "Ctrl+W"))
        e = mb.addMenu("&Edit")
        for a in (self.a_undo, self.a_cut, self.a_copy, self.a_paste):
            e.addAction(a)
        e.addSeparator()
        e.addAction(self._act("Select &All", None, lambda: self._focused_edit().selectAll(), "Ctrl+A"))
        vm = mb.addMenu("&View")
        self.act_bcc = QAction("&All Headers", self, checkable=True)
        self.act_bcc.toggled.connect(self._show_bcc)
        vm.addAction(self.act_bcc)
        ins = mb.addMenu("&Insert")
        ins.addAction(self.a_attach)
        ins.addAction(self._act("&Horizontal Line", None,
                                lambda: self.editor.textCursor().insertHtml("<hr>")))
        ins.addAction(self._act("&Date and Time", None,
                                lambda: self.editor.textCursor().insertText(fmt_date(time.time()))))
        msg = mb.addMenu("&Message")
        msg.addAction(self.a_send)
        msg.addMenu(self.pri_btn.menu()).setText("Set &Priority")

    def _build_format_bar(self):
        tb = QToolBar("Formatting")
        tb.setMovable(False)
        tb.setIconSize(QSize(16, 16))
        tb.setStyleSheet("QToolBar { border-top: 1px solid #FFFFFF; }")
        self.font_box = QFontComboBox()
        self.font_box.setCurrentFont(QFont("Arial"))
        self.font_box.setMaximumWidth(170)
        self.font_box.currentFontChanged.connect(lambda f: self._merge(family=f.family()))
        tb.addWidget(self.font_box)
        self.size_box = QComboBox()
        self.size_box.setEditable(True)
        self.size_box.addItems([str(s) for s in (8, 9, 10, 11, 12, 14, 16, 18, 20, 24, 28, 36)])
        self.size_box.setCurrentText("10")
        self.size_box.setFixedWidth(52)
        self.size_box.textActivated.connect(lambda t: self._merge(size=t))
        tb.addWidget(self.size_box)
        tb.addSeparator()
        self.fmt_actions = {}
        for key, text, sc in (("b", "B", "Ctrl+B"), ("i", "I", "Ctrl+I"), ("u", "U", "Ctrl+U")):
            a = QAction(text, self, checkable=True)
            a.setShortcut(QKeySequence(sc))
            a.triggered.connect(lambda checked, k=key: self._merge(**{k: checked}))
            tb.addAction(a)
            btn = tb.widgetForAction(a)
            f = QFont("Times New Roman", 11)
            f.setBold(key == "b")
            f.setItalic(key == "i")
            f.setUnderline(key == "u")
            btn.setFont(f)
            btn.setFixedWidth(26)
            self.fmt_actions[key] = a
        tb.addAction(self._act("Font Color", "color", self._pick_color))
        tb.addSeparator()
        tb.addAction(self._act("Numbered List", "numbers", lambda: self._list(QTextListFormat.ListDecimal)))
        tb.addAction(self._act("Bulleted List", "bullets", lambda: self._list(QTextListFormat.ListDisc)))
        tb.addSeparator()
        for ic, al in (("al_left", Qt.AlignLeft), ("al_center", Qt.AlignHCenter), ("al_right", Qt.AlignRight)):
            tb.addAction(self._act(ic.replace("al_", "Align ").title(), ic,
                                   lambda a=al: (self.editor.setAlignment(a | Qt.AlignAbsolute), self._touch())))
        tb.addAction(self._act("Insert Horizontal Line", None, lambda: self.editor.textCursor().insertHtml("<hr>")))
        tb.actions()[-1].setText("—")
        return tb

    # -- helpers
    def _focused_edit(self):
        w = QApplication.focusWidget()
        return w if isinstance(w, (QLineEdit, QTextEdit)) else self.editor

    def _touch(self, *_):
        self.dirty = True

    def _title(self):
        s = self.subject.text().strip()
        self.setWindowTitle(s or "New Message")

    def _show_bcc(self, on):
        for w in self.fields["Bcc"]:
            w.setVisible(on)

    def _pick(self, edit):
        d = SelectRecipients(self, self.store)
        if d.exec() and d.chosen():
            cur = [p.strip() for p in edit.text().split(",") if p.strip()]
            edit.setText(", ".join(cur + d.chosen()))
            self._touch()

    def _set_priority(self, v, touch=True):
        self.priority = v
        for val, a in self.pri_actions.items():
            a.setChecked(val == v)
        self.pri_btn.setIcon(icon("high" if v == 1 else "low" if v == 5 else "high"))
        self.statusBar().showMessage({1: "This message is High Priority.", 5: "This message is Low Priority."}
                                     .get(v, ""))
        if touch:
            self._touch()

    def _merge(self, family=None, size=None, b=None, i=None, u=None):
        fmt = QTextCharFormat()
        if family:
            fmt.setFontFamilies([family])
        if size:
            try:
                fmt.setFontPointSize(float(size))
            except ValueError:
                return
        if b is not None:
            fmt.setFontWeight(700 if b else 400)
        if i is not None:
            fmt.setFontItalic(i)
        if u is not None:
            fmt.setFontUnderline(u)
        c = self.editor.textCursor()
        if not c.hasSelection():
            c.select(QTextCursor.WordUnderCursor)
        c.mergeCharFormat(fmt)
        self.editor.mergeCurrentCharFormat(fmt)
        self.editor.setFocus()

    def _pick_color(self):
        col = QColorDialog.getColor(self.editor.textColor(), self, "Font Color")
        if col.isValid():
            fmt = QTextCharFormat()
            fmt.setForeground(col)
            self.editor.mergeCurrentCharFormat(fmt)

    def _list(self, style):
        self.editor.textCursor().createList(style)

    def _sync_format(self, fmt):
        self.fmt_actions["b"].setChecked(int(fmt.fontWeight()) >= 600)
        self.fmt_actions["i"].setChecked(fmt.fontItalic())
        self.fmt_actions["u"].setChecked(fmt.fontUnderline())
        if fmt.fontPointSize() > 0:
            self.size_box.setCurrentText(str(int(fmt.fontPointSize())))

    def _refresh_atts(self):
        self.att_list.clear()
        for name, data, _ in self.attachments:
            self.att_list.addItem(QListWidgetItem(icon("attach"), f"{name} ({max(1, len(data) // 1024)} KB)"))
        on = bool(self.attachments)
        self.att_label.setVisible(on)
        self.att_list.setVisible(on)

    def _att_menu(self, pos):
        row = self.att_list.row(self.att_list.itemAt(pos)) if self.att_list.itemAt(pos) else -1
        if row >= 0:
            m = QMenu(self)
            m.addAction("Remove", lambda: (self.attachments.pop(row), self._refresh_atts(), self._touch()))
            m.exec(self.att_list.mapToGlobal(pos))

    def add_attachment(self):
        paths, _ = QFileDialog.getOpenFileNames(self, "Insert Attachment")
        for p in paths:
            data = Path(p).read_bytes()
            ctype = mimetypes.guess_type(p)[0] or "application/octet-stream"
            self.attachments.append((Path(p).name, data, ctype))
        if paths:
            self._refresh_atts()
            self._touch()

    def keyPressEvent(self, ev):
        if ev.key() == Qt.Key_Delete and self.att_list.hasFocus() and self.att_list.currentRow() >= 0:
            self.attachments.pop(self.att_list.currentRow())
            self._refresh_atts()
            return
        super().keyPressEvent(ev)

    # -- building / sending
    def _account(self):
        return self.cfg.account(self.from_box.currentData()) or self.cfg.default_account()

    def build(self, acct):
        m = EmailMessage()
        if acct:
            m["From"] = formataddr((acct.get("display") or "", acct["email"]))
        for key in ("To", "Cc", "Bcc"):
            pairs = parse_addresses(self.fields[key][1].text())
            if pairs:
                m[key] = ", ".join(formataddr(p) for p in pairs)
        m["Subject"] = self.subject.text()
        m["Date"] = formatdate(localtime=True)
        domain = acct["email"].split("@")[-1] if acct else "localhost"
        m["Message-ID"] = make_msgid(domain=domain)
        for k, v in self.extra_headers.items():
            if v:
                m[k] = v
        if self.priority == 1:
            m["X-Priority"] = "1 (Highest)"
            m["Importance"] = "High"
        elif self.priority == 5:
            m["X-Priority"] = "5 (Lowest)"
            m["Importance"] = "Low"
        m["X-Mailer"] = f"{APP_NAME} {VERSION}"
        m.set_content(self.editor.toPlainText())
        m.add_alternative(self.editor.toHtml(), subtype="html")
        for name, data, ctype in self.attachments:
            maintype, _, subtype = ctype.partition("/")
            m.add_attachment(data, maintype=maintype, subtype=subtype or "octet-stream", filename=name)
        return m.as_bytes()

    def send(self):
        to = [self.fields[k][1].text().strip() for k in ("To", "Cc", "Bcc")]
        if not any(to):
            XPMsg.warning(self, APP_NAME, "The message must have at least one recipient.")
            return
        if not parse_addresses(*to):
            XPMsg.warning(self, APP_NAME, "None of the recipients look like e-mail addresses.\n\n"
                                "Type them like  name@example.com  and separate several with commas.")
            return
        acct = self._account()
        if not acct:
            XPMsg.information(self, APP_NAME, "You need to set up a mail account before you can "
                                    "send mail.\n\nChoose Tools > Accounts in the main window.")
            return
        if not self.subject.text().strip() and XPMsg.question(
                self, APP_NAME, "This message does not have a subject. Do you want to send it anyway?") \
                != QMessageBox.Yes:
            return
        try:
            raw = self.build(acct)
        except Exception as e:
            XPMsg.warning(self, APP_NAME, f"The message could not be created:\n\n{e}\n\n"
                                "Check that the addresses are separated by commas.")
            return
        self.store.add_message("Outbox", raw, account=acct["id"], is_read=1)
        if self.draft_id:
            self.store.delete([self.draft_id])
        self.finished = True
        self.close()
        self.main.message_queued()

    def save_draft(self):
        acct = self._account()
        try:
            raw = self.build(acct)
        except Exception as e:
            XPMsg.warning(self, APP_NAME, f"Could not save the draft:\n\n{e}")
            return False
        if self.draft_id:
            self.store.delete([self.draft_id])
        self.draft_id = self.store.add_message("Drafts", raw, account=acct["id"] if acct else None,
                                               is_read=1)
        self.dirty = False
        self.editor.document().setModified(False)
        self.statusBar().showMessage("Your message has been saved in your 'Drafts' folder.", 4000)
        self.main.refresh_after_change()
        return True

    def closeEvent(self, ev):
        if not self.finished and (self.dirty or self.editor.document().isModified()):
            r = XPMsg.question(self, APP_NAME, "Do you want to save changes to this message?",
                                     QMessageBox.Yes | QMessageBox.No | QMessageBox.Cancel)
            if r == QMessageBox.Cancel or (r == QMessageBox.Yes and not self.save_draft()):
                ev.ignore()
                return
        ev.accept()


# --------------------------------------------------------------------------
# Read-message window (double-click a message)
# --------------------------------------------------------------------------

class MessageWindow(QMainWindow):
    def __init__(self, main, mid):
        super().__init__()
        xp_frame(self)
        self.setAttribute(Qt.WA_DeleteOnClose)
        self.main = main
        self.mid = mid
        tb = QToolBar()
        tb.setMovable(False)
        tb.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        tb.setIconSize(QSize(24, 24))
        self.addToolBar(tb)
        for text, ic, slot in (("Reply", "reply", lambda: main.reply("reply", self.mid)),
                               ("Reply All", "replyall", lambda: main.reply("all", self.mid)),
                               ("Forward", "forward", lambda: main.reply("forward", self.mid)),
                               (None, None, None),
                               ("Print", "print", lambda: main.print_message(self.mid)),
                               ("Delete", "delete", self.delete)):
            if text is None:
                tb.addSeparator()
                continue
            a = tb.addAction(icon(ic), text)
            a.triggered.connect(slot)
        self.pane = PreviewPane(main)
        self.setCentralWidget(self.pane)
        row = main.store.get(mid)
        self.pane.show_message(row)
        self.setWindowTitle(row["subject"] or "(no subject)")
        self.setWindowIcon(icon("read"))
        self.resize(700, 560)
        main.store.set_read([mid], 1)
        main.refresh_after_change()

    def delete(self):
        self.main.delete_ids([self.mid])
        self.close()


# --------------------------------------------------------------------------
# Main window
# --------------------------------------------------------------------------

class MainWindow(QMainWindow):
    def __init__(self, cfg, store):
        super().__init__()
        xp_frame(self)
        self.cfg = cfg
        self.store = store
        self.current = None          # folder name, '__search__', '__root__'
        self.search_term = ""
        self.hide_read = False
        self.preview_id = None
        self.worker = None
        self.sync_dialog = None
        self.windows = []
        self.setWindowIcon(icon("app"))
        self.resize(1040, 720)

        self.read_timer = QTimer(self)
        self.read_timer.setSingleShot(True)
        self.read_timer.timeout.connect(self._mark_preview_read)
        self.check_timer = QTimer(self)
        self.check_timer.timeout.connect(lambda: self.send_receive(manual=False))

        self._build_actions()
        self._build_menus()
        self._build_toolbar()
        self._build_central()
        self._build_statusbar()
        self._build_tray()
        self.apply_view_settings()
        self._restore_state()
        self.refresh_folders()
        self.refresh_contacts()
        self.select_folder("Inbox" if cfg.get("start_in_inbox") else "__root__")
        self.reset_check_timer()

    # ---- actions / menus / toolbar
    def _a(self, key, text, slot, shortcut=None, ic=None, icon_text=None, checkable=False):
        a = QAction(text, self)
        if ic:
            a.setIcon(icon(ic))
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
        if icon_text:
            a.setIconText(icon_text)
        a.setCheckable(checkable)
        if checkable:
            a.toggled.connect(slot)
        else:
            a.triggered.connect(lambda _=False: slot())
        self.acts[key] = a
        return a

    def _build_actions(self):
        self.acts = {}
        A = self._a
        A("new", "&Mail Message", self.compose, "Ctrl+N", "new", "Create Mail")
        A("reply", "&Reply to Sender", lambda: self.reply("reply"), "Ctrl+R", "reply", "Reply")
        A("replyall", "Reply to &All", lambda: self.reply("all"), "Ctrl+Shift+R", "replyall", "Reply All")
        A("forward", "&Forward", lambda: self.reply("forward"), "Ctrl+F", "forward", "Forward")
        A("print", "&Print...", self.print_message, "Ctrl+P", "print", "Print")
        A("delete", "&Delete Message", self.delete_selected, QKeySequence.Delete, "delete", "Delete")
        A("sendrecv", "Send and Recei&ve All", lambda: self.send_receive(), "Ctrl+M", "sendrecv", "Send/Recv")
        A("recv", "&Receive All", lambda: self.send_receive(send=False))
        A("sendall", "&Send All", lambda: self.send_receive(receive=False))
        A("addresses", "&Address Book...", self.open_address_book, "Ctrl+Shift+B", "addresses", "Addresses")
        A("find", "&Message...", self.find_messages, "Ctrl+Shift+F", "find", "Find")
        A("read", "Mark as &Read", lambda: self.set_read(1), "Ctrl+Q", "read")
        A("unread", "Mark as &Unread", lambda: self.set_read(0), None, "unread")
        A("allread", "Mark All Read", self.mark_all_read, "Ctrl+Shift+A")
        A("flag", "&Flag Message", self.toggle_flag, None, "flag")
        A("move", "Mo&ve to Folder...", self.move_selected, "Ctrl+Shift+V")
        A("newfolder", "&Folder...", self.new_folder, "Ctrl+Shift+E", "folder")
        A("empty", "Empty 'Deleted Items' Folder", self.empty_deleted, None, "deleted")
        A("saveas", "Save &As...", self.save_as)
        A("import", "&Messages (.eml)...", self.import_eml)
        A("accounts", "&Accounts...", self.open_accounts, None, "app")
        A("options", "&Options...", self.open_options)
        A("about", f"&About {APP_NAME}", self.about)
        A("exit", "E&xit", self.close)
        A("open", "&Open", self.open_selected, "Ctrl+O")
        A("selall", "Select &All", lambda: self.msg_list.selectAll(), "Ctrl+A")
        A("v_folders", "&Folder List", lambda on: self.toggle_setting("show_folders", on), checkable=True)
        A("v_contacts", "&Contacts", lambda on: self.toggle_setting("show_contacts", on), checkable=True)
        A("v_preview", "&Preview Pane", lambda on: self.toggle_setting("show_preview", on), checkable=True)
        A("v_toolbar", "&Toolbar", lambda on: self.toggle_setting("show_toolbar", on), checkable=True)
        A("v_status", "&Status Bar", lambda on: self.toggle_setting("show_statusbar", on), checkable=True)
        A("v_hideread", "&Hide Read Messages", self._set_hide_read, checkable=True)

    def _build_menus(self):
        mb = self.menuBar()
        f = mb.addMenu("&File")
        nm = f.addMenu("&New")
        nm.addAction(self.acts["new"])
        nm.addAction(self.acts["newfolder"])
        nm.addAction(self._contact_action())
        f.addAction(self.acts["open"])
        f.addAction(self.acts["saveas"])
        f.addSeparator()
        im = f.addMenu("&Import")
        im.addAction(self.acts["import"])
        f.addSeparator()
        f.addAction(self.acts["print"])
        f.addSeparator()
        f.addAction(self.acts["exit"])
        e = mb.addMenu("&Edit")
        e.addAction(self.acts["selall"])
        e.addSeparator()
        e.addAction(self.acts["delete"])
        e.addAction(self.acts["empty"])
        e.addSeparator()
        e.addAction(self.acts["read"])
        e.addAction(self.acts["unread"])
        e.addAction(self.acts["allread"])
        e.addSeparator()
        e.addAction(self.acts["move"])
        fm = e.addMenu("&Find")
        fm.addAction(self.acts["find"])
        v = mb.addMenu("&View")
        cv = v.addMenu("Current &View")
        cv.addAction(self.acts["v_hideread"])
        v.addSeparator()
        lay = v.addMenu("&Layout")
        for k in ("v_folders", "v_contacts", "v_preview", "v_toolbar", "v_status"):
            lay.addAction(self.acts[k])
        t = mb.addMenu("&Tools")
        sr = t.addMenu(icon("sendrecv"), "S&end and Receive")
        sr.addAction(self.acts["sendrecv"])
        sr.addSeparator()
        sr.addAction(self.acts["recv"])
        sr.addAction(self.acts["sendall"])
        t.addSeparator()
        t.addAction(self.acts["addresses"])
        t.addSeparator()
        t.addAction(self.acts["accounts"])
        t.addAction(self.acts["options"])
        m = mb.addMenu("&Message")
        m.addAction(self.acts["new"])
        m.addSeparator()
        m.addAction(self.acts["reply"])
        m.addAction(self.acts["replyall"])
        m.addAction(self.acts["forward"])
        m.addSeparator()
        m.addAction(self.acts["flag"])
        m.addAction(self.acts["move"])
        h = mb.addMenu("&Help")
        h.addAction(self.acts["about"])
        corner = QLabel()
        corner.setPixmap(make_pixmap("app", 18))
        corner.setContentsMargins(0, 0, 6, 0)
        mb.setCornerWidget(corner, Qt.TopRightCorner)

    def _contact_action(self):
        a = QAction(icon("contact"), "&Contact...", self)
        a.triggered.connect(lambda _=False: self.new_contact())
        return a

    def _build_toolbar(self):
        tb = QToolBar("Standard Buttons")
        tb.setObjectName("mainToolbar")
        tb.setMovable(False)
        tb.setToolButtonStyle(Qt.ToolButtonTextUnderIcon)
        tb.setIconSize(QSize(24, 24))
        self.addToolBar(tb)
        self.toolbar = tb
        for key in ("new", None, "reply", "replyall", "forward", None, "print", "delete", None,
                    "sendrecv", None, "addresses", "find"):
            if key is None:
                tb.addSeparator()
            else:
                tb.addAction(self.acts[key])
        # little drop-down arrows on Create Mail and Send/Recv, like the original
        newmenu = QMenu(self)
        newmenu.addAction(self.acts["new"])
        newmenu.addAction(self._contact_action())
        tb.widgetForAction(self.acts["new"]).setMenu(newmenu)
        tb.widgetForAction(self.acts["new"]).setPopupMode(QToolButton.MenuButtonPopup)
        srmenu = QMenu(self)
        for k in ("sendrecv", "recv", "sendall"):
            srmenu.addAction(self.acts[k])
        tb.widgetForAction(self.acts["sendrecv"]).setMenu(srmenu)
        tb.widgetForAction(self.acts["sendrecv"]).setPopupMode(QToolButton.MenuButtonPopup)

    def _build_central(self):
        central = QWidget()
        v = QVBoxLayout(central)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)

        band = QFrame()
        band.setObjectName("folderBand")
        band.setFixedHeight(34)
        bl = QHBoxLayout(band)
        bl.setContentsMargins(8, 2, 10, 2)
        self.band_icon = QLabel()
        self.band_title = QLabel()
        self.band_title.setObjectName("bandTitle")
        self.band_identity = QLabel("Main Identity")
        bl.addWidget(self.band_icon)
        bl.addWidget(self.band_title)
        bl.addStretch()
        bl.addWidget(self.band_identity)
        v.addWidget(band)

        self.hsplit = QSplitter(Qt.Horizontal)
        self.hsplit.setChildrenCollapsible(False)
        self.lsplit = QSplitter(Qt.Vertical)
        self.lsplit.setChildrenCollapsible(False)

        self.folder_tree = QTreeWidget()
        self.folder_tree.setHeaderHidden(True)
        self.folder_tree.setIconSize(QSize(16, 16))
        self.folder_tree.setItemDelegate(FolderDelegate(self.folder_tree))
        self.folder_tree.setIndentation(14)
        self.folder_tree.currentItemChanged.connect(self._folder_changed)
        self.folder_tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.folder_tree.customContextMenuRequested.connect(self._folder_menu)
        self.folder_panel = Panel("Folders", self.folder_tree,
                                  on_close=lambda: self.acts["v_folders"].setChecked(False))

        self.contact_list = QListWidget()
        self.contact_list.setIconSize(QSize(16, 16))
        self.contact_list.itemDoubleClicked.connect(
            lambda it: self.compose(to=it.data(Qt.UserRole)))
        cm = QMenu(self)
        cm.addAction(icon("contact"), "New &Contact...", self.new_contact)
        cm.addAction(icon("new"), "New &Message", self._mail_selected_contact)
        cm.addSeparator()
        cm.addAction(icon("addresses"), "Open &Address Book", self.open_address_book)
        self.contacts_panel = Panel("Contacts", self.contact_list,
                                    on_close=lambda: self.acts["v_contacts"].setChecked(False), menu=cm)
        self.lsplit.addWidget(self.folder_panel)
        self.lsplit.addWidget(self.contacts_panel)
        self.lsplit.setSizes([420, 200])

        self.stack = QStackedWidget()
        # start page
        start = QWidget()
        sv = QVBoxLayout(start)
        sv.setContentsMargins(0, 0, 0, 0)
        sv.setSpacing(0)
        self.start_page = QTextBrowser()
        self.start_page.setOpenLinks(False)
        self.start_page.anchorClicked.connect(self._start_link)
        for name in ("new", "inbox", "addresses", "find", "app", "sendrecv"):
            self.start_page.document().addResource(QTextDocument.ImageResource, QUrl(f"icon:{name}"),
                                                   make_pixmap(name, 32))
        sv.addWidget(self.start_page, 1)
        self.start_chk = QCheckBox(f"When {APP_NAME} starts, go directly to my Inbox.")
        self.start_chk.setStyleSheet("QCheckBox { background:#FFFFFF; padding:6px 10px; "
                                     "border:1px solid #7F9DB9; border-top:none; }")
        self.start_chk.setChecked(self.cfg.get("start_in_inbox"))
        self.start_chk.toggled.connect(lambda on: (self.cfg.set("start_in_inbox", on), self.cfg.save()))
        sv.addWidget(self.start_chk)
        self.stack.addWidget(start)

        # message list + preview
        self.vsplit = QSplitter(Qt.Vertical)
        self.vsplit.setChildrenCollapsible(False)
        self.msg_list = QTreeWidget()
        self.msg_list.setRootIsDecorated(False)
        self.msg_list.setUniformRowHeights(True)
        self.msg_list.setSelectionMode(QAbstractItemView.ExtendedSelection)
        self.msg_list.setSortingEnabled(True)
        self.msg_list.setIconSize(QSize(16, 16))
        self.msg_list.setAllColumnsShowFocus(True)
        self.msg_list.setHeaderLabels(["!", "", "", "From", "Subject", "Received"])
        hi = self.msg_list.headerItem()
        hi.setIcon(1, icon("attach"))
        hi.setIcon(2, icon("flag"))
        hdrv = self.msg_list.header()
        hdrv.setSectionsMovable(False)
        for col, w in ((0, 22), (1, 24), (2, 24)):
            hdrv.setSectionResizeMode(col, QHeaderView.Fixed)
            self.msg_list.setColumnWidth(col, w)
        self.msg_list.setColumnWidth(3, 210)
        hdrv.setSectionResizeMode(4, QHeaderView.Stretch)
        self.msg_list.setColumnWidth(5, 150)
        hdrv.setStretchLastSection(False)
        self.msg_list.sortByColumn(5, Qt.DescendingOrder)
        self.msg_list.itemSelectionChanged.connect(self._selection_changed)
        self.msg_list.itemDoubleClicked.connect(lambda *_: self.open_selected())
        self.msg_list.setContextMenuPolicy(Qt.CustomContextMenu)
        self.msg_list.customContextMenuRequested.connect(self._msg_menu)
        self.preview = PreviewPane(self)
        self.vsplit.addWidget(self.msg_list)
        self.vsplit.addWidget(self.preview)
        self.vsplit.setSizes([260, 380])
        self.stack.addWidget(self.vsplit)

        self.hsplit.addWidget(self.lsplit)
        self.hsplit.addWidget(self.stack)
        self.hsplit.setStretchFactor(1, 1)
        self.hsplit.setSizes([210, 830])
        v.addWidget(self.hsplit, 1)
        self.setCentralWidget(central)

    def _build_statusbar(self):
        sb = self.statusBar()
        sb.setSizeGripEnabled(True)
        self.status_left = QLabel("")
        self.status_task = QLabel("")
        self.status_online = QLabel("  Working Online  ")
        sb.addWidget(self.status_left, 1)
        sb.addPermanentWidget(self.status_task)
        sb.addPermanentWidget(self.status_online)

    def _build_tray(self):
        self.tray = None
        if QSystemTrayIcon.isSystemTrayAvailable():
            self.tray = QSystemTrayIcon(icon("app"), self)
            self.tray.setToolTip(APP_NAME)
            self.tray.activated.connect(self._tray_clicked)
            self.tray.messageClicked.connect(self._tray_clicked)
            self.tray.show()

    def _tray_clicked(self, *_):
        self.tray.setIcon(icon("app"))
        self.showNormal()
        self.activateWindow()
        self.select_folder("Inbox")

    # ---- view settings
    def apply_view_settings(self):
        mapping = {"v_folders": "show_folders", "v_contacts": "show_contacts", "v_preview": "show_preview",
                   "v_toolbar": "show_toolbar", "v_status": "show_statusbar"}
        for act, key in mapping.items():
            self.acts[act].blockSignals(True)
            self.acts[act].setChecked(bool(self.cfg.get(key)))
            self.acts[act].blockSignals(False)
        self.folder_panel.setVisible(self.cfg.get("show_folders"))
        self.contacts_panel.setVisible(self.cfg.get("show_contacts"))
        self.lsplit.setVisible(self.cfg.get("show_folders") or self.cfg.get("show_contacts"))
        self.preview.setVisible(self.cfg.get("show_preview"))
        self.toolbar.setVisible(self.cfg.get("show_toolbar"))
        self.statusBar().setVisible(self.cfg.get("show_statusbar"))

    def toggle_setting(self, key, on):
        self.cfg.set(key, bool(on))
        self.cfg.save()
        self.apply_view_settings()

    def _set_hide_read(self, on):
        self.hide_read = on
        self.load_messages()

    def _restore_state(self):
        st = self.cfg.data.get("window", {})
        try:
            if st.get("geometry"):
                self.restoreGeometry(QByteArray.fromBase64(st["geometry"].encode()))
            for name in ("hsplit", "lsplit", "vsplit"):
                if st.get(name):
                    getattr(self, name).restoreState(QByteArray.fromBase64(st[name].encode()))
            if st.get("header"):
                self.msg_list.header().restoreState(QByteArray.fromBase64(st["header"].encode()))
        except Exception:
            pass

    def _save_state(self):
        enc = lambda ba: bytes(ba.toBase64()).decode()
        self.cfg.data["window"] = {
            "geometry": enc(self.saveGeometry()), "hsplit": enc(self.hsplit.saveState()),
            "lsplit": enc(self.lsplit.saveState()), "vsplit": enc(self.vsplit.saveState()),
            "header": enc(self.msg_list.header().saveState())}
        self.cfg.save()

    def closeEvent(self, ev):
        self._save_state()
        if self.worker and self.worker.isRunning():
            self.worker.wait(5000)
        for w in QApplication.topLevelWidgets():
            if isinstance(w, ComposeWindow) and w.isVisible():
                if not w.close():
                    ev.ignore()
                    return
        if self.tray:
            self.tray.hide()
        ev.accept()
        QApplication.quit()

    # ---- folders
    def refresh_folders(self):
        counts = self.store.counts()
        current = self.current
        self.folder_tree.blockSignals(True)
        self.folder_tree.clear()
        root = QTreeWidgetItem([APP_NAME])
        root.setIcon(0, icon("app"))
        root.setData(0, ID_ROLE, "__root__")
        self.folder_tree.addTopLevelItem(root)
        local = QTreeWidgetItem(["Local Folders"])
        local.setIcon(0, icon("local"))
        local.setData(0, ID_ROLE, "__root__")
        root.addChild(local)
        for r in self.store.folders():
            it = QTreeWidgetItem([r["name"]])
            it.setIcon(0, icon(FOLDER_ICONS.get(r["name"], "folder")))
            it.setData(0, ID_ROLE, r["name"])
            it.setData(0, COUNT_ROLE, counts.get(r["name"], 0))
            local.addChild(it)
        self.folder_tree.expandAll()
        self.folder_tree.blockSignals(False)
        self._select_tree(current or "__root__", notify=False)

    def refresh_counts(self):
        counts = self.store.counts()

        def walk(item):
            name = item.data(0, ID_ROLE)
            if name not in ("__root__", None):
                item.setData(0, COUNT_ROLE, counts.get(name, 0))
            for i in range(item.childCount()):
                walk(item.child(i))
        for i in range(self.folder_tree.topLevelItemCount()):
            walk(self.folder_tree.topLevelItem(i))
        self.folder_tree.viewport().update()
        unread = counts.get("Inbox", 0)
        if self.tray:
            self.tray.setToolTip(f"{APP_NAME} - {unread} unread message(s)" if unread else APP_NAME)

    def _select_tree(self, name, notify=True):
        def walk(item):
            if item.data(0, ID_ROLE) == name and (name != "__root__" or item.parent() is None):
                return item
            for i in range(item.childCount()):
                f = walk(item.child(i))
                if f:
                    return f
            return None
        for i in range(self.folder_tree.topLevelItemCount()):
            found = walk(self.folder_tree.topLevelItem(i))
            if found:
                if not notify:
                    self.folder_tree.blockSignals(True)
                self.folder_tree.setCurrentItem(found)
                self.folder_tree.blockSignals(False)
                return True
        return False

    def select_folder(self, name):
        if not self._select_tree(name) or self.current != name:
            self._open_folder(name)

    def _folder_changed(self, item, _prev=None):
        if item:
            self._open_folder(item.data(0, ID_ROLE))

    def _open_folder(self, name):
        self.current = name
        self.search_term = "" if name != "__search__" else self.search_term
        if name == "__root__":
            self.stack.setCurrentIndex(0)
            self.band_icon.setPixmap(make_pixmap("app", 24))
            self.band_title.setText(APP_NAME)
            self.setWindowTitle(APP_NAME)
            self._render_start_page()
            self.status_left.setText("")
            self._update_actions()
            return
        self.stack.setCurrentIndex(1)
        if name == "__search__":
            self.band_icon.setPixmap(make_pixmap("find", 24))
            self.band_title.setText(f"Find: '{self.search_term}'")
            self.setWindowTitle(f"Find Message - {APP_NAME}")
        else:
            self.band_icon.setPixmap(make_pixmap(FOLDER_ICONS.get(name, "folder"), 24))
            self.band_title.setText(name)
            self.setWindowTitle(f"{name} - {APP_NAME}")
        outgoing = name in OUTGOING_FOLDERS
        self.msg_list.headerItem().setText(3, "To" if outgoing else "From")
        self.msg_list.headerItem().setText(5, "Sent" if outgoing else "Received")
        self.load_messages()

    def _render_start_page(self):
        unread = self.store.counts().get("Inbox", 0)
        ident = self.band_identity.text()
        tip = random.choice(TIPS)
        T = THEME
        acct_line = ("" if self.cfg.accounts else
                     "<p><img src='icon:app' width=16 height=16> <a href='app:accounts'><b>Set up a Mail "
                     "account...</b></a></p>")
        self.start_page.setHtml(f"""
<table width="100%" cellspacing="0" cellpadding="10" bgcolor="{T['start_band']}"><tr><td>
<span style="color:#FFFFFF; font-size:20pt; font-weight:bold; font-family:Tahoma">{APP_NAME}</span>
<span style="color:{T['start_band_text']}; font-size:10pt">&nbsp;&nbsp;for {html.escape(ident)}</span></td></tr></table>
<table width="100%" cellspacing="0" cellpadding="14"><tr>
<td width="62%" valign="top" style="font-family:Tahoma; font-size:9pt">
<p style="font-size:12pt; color:{T['heading']}"><b>E-mail</b></p>
<p><img src="icon:inbox" width=16 height=16> There {'is' if unread == 1 else 'are'}
<a href="app:inbox"><b>{unread} unread Mail</b></a> message{'s' if unread != 1 else ''} in your Inbox</p>
<p><img src="icon:new" width=16 height=16> <a href="app:compose">Create a new Mail message</a></p>
<p><img src="icon:inbox" width=16 height=16> <a href="app:inbox">Read Mail</a></p>
<p><img src="icon:sendrecv" width=16 height=16> <a href="app:sendrecv">Send and Receive All</a></p>
{acct_line}
<p style="font-size:12pt; color:{T['heading']}"><br><b>Contacts</b></p>
<p><img src="icon:addresses" width=16 height=16> <a href="app:addressbook">Open the Address Book...</a></p>
<p><img src="icon:find" width=16 height=16> <a href="app:find">Find Messages...</a></p>
</td>
<td valign="top" bgcolor="{T['start_side']}" style="font-family:Tahoma; font-size:9pt">
<p style="color:{T['heading']}; font-size:10pt"><b>Did you know?</b></p><p>{tip}</p></td>
</tr></table>""")

    def _start_link(self, url):
        cmd = url.toString().split(":", 1)[-1]
        {"inbox": lambda: self.select_folder("Inbox"), "compose": self.compose,
         "addressbook": self.open_address_book, "find": self.find_messages,
         "accounts": self.open_accounts, "sendrecv": self.send_receive}.get(cmd, lambda: None)()

    def _folder_menu(self, pos):
        item = self.folder_tree.itemAt(pos)
        name = item.data(0, ID_ROLE) if item else None
        m = QMenu(self)
        m.addAction(self.acts["newfolder"])
        if name and name not in SPECIAL_FOLDERS and name != "__root__":
            m.addAction("&Rename", lambda: self.rename_folder(name))
            m.addAction(icon("delete"), "&Delete", lambda: self.delete_folder(name))
        if name and name != "__root__":
            m.addSeparator()
            m.addAction("Mark All Read", lambda: (self.store.mark_all_read(name), self.refresh_after_change()))
        if name == "Deleted Items":
            m.addAction(self.acts["empty"])
        m.exec(self.folder_tree.viewport().mapToGlobal(pos))

    def new_folder(self):
        name, ok = xp_get_text(self, "Create Folder", "Folder name:")
        name = name.strip()
        if ok and name:
            if any(r["name"].lower() == name.lower() for r in self.store.folders()):
                XPMsg.warning(self, APP_NAME, "A folder with that name already exists.")
                return
            self.store.add_folder(name)
            self.refresh_folders()

    def rename_folder(self, old):
        new, ok = xp_get_text(self, "Rename Folder", "New name:", QLineEdit.Normal, old)
        new = new.strip()
        if ok and new and new != old:
            if any(r["name"].lower() == new.lower() for r in self.store.folders()):
                XPMsg.warning(self, APP_NAME, "A folder with that name already exists.")
                return
            self.store.rename_folder(old, new)
            if self.current == old:
                self.current = new
            self.refresh_folders()
            self._open_folder(self.current)

    def delete_folder(self, name):
        if XPMsg.question(self, APP_NAME, f"Are you sure you want to delete the '{name}' folder?\n\n"
                                "Its messages will be moved to Deleted Items.") == QMessageBox.Yes:
            self.store.delete_folder(name)
            if self.current == name:
                self.current = "Inbox"
            self.refresh_folders()
            self._open_folder(self.current)

    def empty_deleted(self):
        if XPMsg.question(self, APP_NAME, "Are you sure you want to permanently delete all the "
                                "messages in the 'Deleted Items' folder?") == QMessageBox.Yes:
            self.store.empty_folder("Deleted Items")
            self.refresh_after_change()

    # ---- contacts
    def refresh_contacts(self):
        self.contact_list.clear()
        rows = self.store.contacts()
        for r in rows:
            it = QListWidgetItem(icon("contact"), r["name"] or r["email"])
            it.setData(Qt.UserRole, formataddr((r["name"] or "", r["email"] or "")))
            self.contact_list.addItem(it)
        if not rows:
            hint = QListWidgetItem("There are no contacts to display. Click on Contacts to create "
                                   "a new contact.")
            hint.setFlags(Qt.NoItemFlags)
            hint.setForeground(QColor("#6D6D6D"))
            self.contact_list.setWordWrap(True)
            self.contact_list.addItem(hint)

    def _mail_selected_contact(self):
        it = self.contact_list.currentItem()
        self.compose(to=it.data(Qt.UserRole) if it and it.data(Qt.UserRole) else "")

    def new_contact(self, name="", email=""):
        d = ContactDialog(self, name=name, email=email)
        if d.exec():
            self.store.save_contact(None, *d.values())
            self.refresh_contacts()

    def open_address_book(self):
        ab = AddressBook(self)
        ab.show()

    # ---- message list
    def load_messages(self):
        if self.current in (None, "__root__"):
            return
        prev_ids = set(self._selected_ids())
        if self.current == "__search__":
            rows = self.store.search(self.search_term)
        else:
            rows = self.store.list(self.current, self.hide_read)
        outgoing = self.current in OUTGOING_FOLDERS
        bold = QFont()
        bold.setBold(True)
        self.msg_list.setSortingEnabled(False)
        self.msg_list.blockSignals(True)
        self.msg_list.clear()
        items = []
        for r in rows:
            it = MsgItem()
            who = r["recipients"] if outgoing else r["sender"]
            it.setData(0, ID_ROLE, r["id"])
            if r["priority"] == 1:
                it.setIcon(0, icon("high"))
            elif r["priority"] == 5:
                it.setIcon(0, icon("low"))
            it.setData(0, SORT_ROLE, r["priority"])
            if r["has_attach"]:
                it.setIcon(1, icon("attach"))
            it.setData(1, SORT_ROLE, -r["has_attach"])
            if r["flagged"]:
                it.setIcon(2, icon("flag"))
            it.setData(2, SORT_ROLE, -r["flagged"])
            it.setIcon(3, icon("read" if r["is_read"] else "unread"))
            it.setText(3, display_name(who) or "(unknown)")
            it.setToolTip(3, who)
            it.setText(4, r["subject"] or "(no subject)")
            it.setText(5, fmt_date(r["ts"]))
            it.setData(5, SORT_ROLE, r["ts"])
            if not r["is_read"]:
                for c in range(6):
                    it.setFont(c, bold)
            items.append(it)
        self.msg_list.addTopLevelItems(items)
        self.msg_list.setSortingEnabled(True)
        for i in range(self.msg_list.topLevelItemCount()):
            it = self.msg_list.topLevelItem(i)
            if it.data(0, ID_ROLE) in prev_ids:
                it.setSelected(True)
        self.msg_list.blockSignals(False)
        self._selection_changed()
        self._update_status()

    def _update_status(self):
        n = self.msg_list.topLevelItemCount()
        unread = sum(1 for i in range(n) if self.msg_list.topLevelItem(i).font(3).bold())
        self.status_left.setText(f"{n} message(s), {unread} unread")

    def _selected_ids(self):
        return [it.data(0, ID_ROLE) for it in self.msg_list.selectedItems()]

    def _single_id(self):
        ids = self._selected_ids()
        return ids[0] if len(ids) == 1 else None

    def _update_actions(self):
        ids = self._selected_ids() if self.current not in (None, "__root__") else []
        one = len(ids) == 1
        for k in ("reply", "replyall", "forward", "print", "saveas", "open"):
            self.acts[k].setEnabled(one)
        for k in ("delete", "read", "unread", "flag", "move"):
            self.acts[k].setEnabled(bool(ids))

    def _selection_changed(self):
        self._update_actions()
        mid = self._single_id()
        self.read_timer.stop()
        if mid is None:
            self.preview_id = None
            self.preview.clear()
            return
        if mid == self.preview_id:
            return
        row = self.store.get(mid)
        if not row:
            return
        self.preview_id = mid
        self.preview.show_message(row)
        if not row["is_read"] and self.preview.isVisible():
            delay = int(self.cfg.get("read_delay"))
            if delay <= 0:
                self._mark_preview_read()
            else:
                self.read_timer.start(delay * 1000)

    def _mark_preview_read(self):
        if self.preview_id:
            self._set_read_ids([self.preview_id], 1)

    def _set_read_ids(self, ids, value):
        self.store.set_read(ids, value)
        normal = QFont()
        bold = QFont()
        bold.setBold(True)
        idset = set(ids)
        for i in range(self.msg_list.topLevelItemCount()):
            it = self.msg_list.topLevelItem(i)
            if it.data(0, ID_ROLE) in idset:
                for c in range(6):
                    it.setFont(c, normal if value else bold)
                it.setIcon(3, icon("read" if value else "unread"))
        self._update_status()
        self.refresh_counts()

    def set_read(self, value):
        self._set_read_ids(self._selected_ids(), value)

    def mark_all_read(self):
        if self.current not in (None, "__root__", "__search__"):
            self.store.mark_all_read(self.current)
            self.refresh_after_change()

    def toggle_flag(self):
        ids = self._selected_ids()
        if ids:
            row = self.store.get(ids[0])
            self.store.set_flag(ids, 0 if row["flagged"] else 1)
            self.load_messages()

    def _msg_menu(self, pos):
        if not self.msg_list.itemAt(pos):
            return
        m = QMenu(self)
        m.addAction(self.acts["open"])
        m.addAction(self.acts["print"])
        m.addSeparator()
        m.addAction(self.acts["reply"])
        m.addAction(self.acts["replyall"])
        m.addAction(self.acts["forward"])
        m.addSeparator()
        m.addAction(self.acts["read"])
        m.addAction(self.acts["unread"])
        m.addAction(self.acts["flag"])
        m.addAction(self.acts["move"])
        m.addSeparator()
        mid = self._single_id()
        if mid:
            row = self.store.get(mid)
            who = row["sender"]
            name, addr = (parse_addresses(who) or [("", "")])[0]
            if addr:
                m.addAction(icon("contact"), "Add Sender to Address Book",
                            lambda: self.new_contact(name, addr))
        m.addAction(self.acts["delete"])
        m.exec(self.msg_list.viewport().mapToGlobal(pos))

    def delete_selected(self):
        if self.focusWidget() is self.folder_tree:
            it = self.folder_tree.currentItem()
            name = it.data(0, ID_ROLE) if it else None
            if name and name not in SPECIAL_FOLDERS and name not in ("__root__", "__search__"):
                self.delete_folder(name)
            return
        self.delete_ids(self._selected_ids())

    def delete_ids(self, ids):
        if not ids:
            return
        folders = {self.store.get(i)["folder"] for i in ids if self.store.get(i)}
        if folders == {"Deleted Items"}:
            if XPMsg.question(self, APP_NAME, "Are you sure you want to permanently delete the "
                                    "selected message(s)?") != QMessageBox.Yes:
                return
            self.store.delete(ids)
        else:
            self.store.move(ids, "Deleted Items")
        # select the next message, like OE does
        idx = self.msg_list.indexOfTopLevelItem(self.msg_list.selectedItems()[-1]) \
            if self.msg_list.selectedItems() else -1
        self.preview_id = None
        self.msg_list.clearSelection()
        self.refresh_after_change()
        if idx >= 0 and self.msg_list.topLevelItemCount():
            idx = min(idx, self.msg_list.topLevelItemCount() - 1)
            self.msg_list.setCurrentItem(self.msg_list.topLevelItem(idx))

    def move_selected(self):
        ids = self._selected_ids()
        if not ids:
            return
        names = [r["name"] for r in self.store.folders()]
        target, ok = xp_get_item(self, "Move", "Move the selected message(s) to:", names, 0, False)
        if ok and target:
            self.store.move(ids, target)
            self.refresh_after_change()

    def open_selected(self):
        mid = self._single_id()
        if not mid:
            return
        row = self.store.get(mid)
        if row["folder"] in ("Drafts", "Outbox"):
            self.open_draft(row)
        else:
            w = MessageWindow(self, mid)
            w.show()

    def refresh_after_change(self):
        self.refresh_counts()
        if self.current == "__root__":
            self._render_start_page()
        else:
            self.load_messages()

    def find_messages(self):
        term, ok = xp_get_text(self, "Find Message",
                                        "Find messages where From, To or Subject contains:")
        term = term.strip()
        if ok and term:
            self.search_term = term
            self.folder_tree.blockSignals(True)
            self.folder_tree.clearSelection()
            self.folder_tree.setCurrentItem(None)
            self.folder_tree.blockSignals(False)
            self.current = "__search__"
            self._open_folder("__search__")

    # ---- composing
    def compose(self, **kw):
        w = ComposeWindow(self, **kw)
        w.show()
        return w

    def open_draft(self, row):
        m = parse_msg(row["raw"])
        try:
            part = m.get_body(preferencelist=("html", "plain"))
            body = _part_text(part) if part else ""
            if part is not None and part.get_content_type() != "text/html":
                body = "<div style='white-space:pre-wrap'>" + html.escape(body) + "</div>"
        except Exception:
            body = ""
        atts = [(p.get_filename() or "attachment", p.get_payload(decode=True) or b"", p.get_content_type())
                for p in attachments_of(m)]
        extra = {k: hdr(m, k) for k in ("In-Reply-To", "References")}
        self.compose(to=hdr(m, "To"), cc=hdr(m, "Cc"), bcc=hdr(m, "Bcc"), subject=hdr(m, "Subject"),
                     html_body=body, attachments=atts, extra_headers=extra, draft_id=row["id"],
                     account_id=row["account"], priority=msg_priority(m))

    def reply(self, mode, mid=None):
        mid = mid or self._single_id()
        if not mid:
            return
        row = self.store.get(mid)
        m = parse_msg(row["raw"])
        mine = {a.get("email", "").lower() for a in self.cfg.accounts}
        frm = hdr(m, "Reply-To") or hdr(m, "From")
        subject = hdr(m, "Subject")
        to = cc = ""
        if mode != "forward":
            to = frm
            if mode == "all":
                skip = mine | {a.lower() for _, a in parse_addresses(frm)}
                others = [formataddr(x) for x in parse_addresses(hdr(m, "To"), hdr(m, "Cc"))
                          if x[1] and x[1].lower() not in skip]
                cc = ", ".join(dict.fromkeys(others))
            if not re.match(r"(?i)^re:", subject):
                subject = "Re: " + subject
        elif not re.match(r"(?i)^(fw|fwd):", subject):
            subject = "Fw: " + subject
        lines = [("From", hdr(m, "From")), ("To", hdr(m, "To")), ("Cc", hdr(m, "Cc")),
                 ("Sent", fmt_date(row["ts"])), ("Subject", hdr(m, "Subject"))]
        head = "".join(f"<b>{k}:</b> {html.escape(v)}<br>" for k, v in lines if v)
        quoted = (f"<p></p><p></p><blockquote><div>----- Original Message ----- </div>"
                  f"<div style='background:#E4E4E4'>{head}</div><br>"
                  f"<div style='white-space:pre-wrap'>{html.escape(body_plain(m))}</div></blockquote>")
        atts = []
        if mode == "forward":
            atts = [(p.get_filename() or "attachment", p.get_payload(decode=True) or b"", p.get_content_type())
                    for p in attachments_of(m)]
        extra = {}
        msgid = hdr(m, "Message-ID")
        if mode != "forward" and msgid:
            extra = {"In-Reply-To": msgid, "References": (hdr(m, "References") + " " + msgid).strip()}
        acct_id = row["account"] if self.cfg.account(row["account"]) else None
        self.compose(to=to, cc=cc, subject=subject, html_body=quoted, attachments=atts,
                     extra_headers=extra, account_id=acct_id)

    def message_queued(self):
        self.refresh_after_change()
        if self.cfg.get("send_immediately"):
            self.send_receive(manual=False, receive=False)

    # ---- send / receive
    def reset_check_timer(self):
        self.check_timer.stop()
        if self.cfg.get("check_enabled") and self.cfg.accounts:
            self.check_timer.start(int(self.cfg.get("check_minutes")) * 60 * 1000)

    def send_receive(self, manual=True, send=True, receive=True):
        if self.worker and self.worker.isRunning():
            if manual and self.sync_dialog:
                self.sync_dialog.show()
            return
        if not self.cfg.accounts:
            if manual:
                if XPMsg.question(self, APP_NAME, "You haven't set up a mail account yet.\n\n"
                                        "Would you like to set one up now?") == QMessageBox.Yes:
                    self.open_accounts()
            return
        self.worker = SyncWorker(self.cfg.accounts, self.store.path, int(self.cfg.get("fetch_limit")),
                                 send=send, receive=receive)
        self.sync_dialog = SyncDialog(self)
        self.worker.progress.connect(self.sync_dialog.set_status)
        self.worker.progress.connect(self.status_task.setText)
        self.worker.error.connect(self.sync_dialog.add_error)
        self.worker.done.connect(self._sync_done)
        if manual:
            self.sync_dialog.show()
        self.status_online.setText("  Connecting...  ")
        self.worker.start()

    def _sync_done(self, new):
        self.status_task.setText("")
        self.status_online.setText("  Working Online  ")
        if self.sync_dialog:
            self.sync_dialog.finish()
        self.refresh_after_change()
        if new:
            if self.cfg.get("play_sound"):
                play_new_mail_sound()
            if self.tray:
                self.tray.setIcon(icon("unread"))
                self.tray.showMessage(APP_NAME, f"You have {new} new message(s).",
                                      icon("unread"), 6000)

    # ---- attachments / files / print
    def open_attachment(self, name, data):
        ext = Path(name).suffix.lower()
        if ext in BLOCKED_EXT:
            XPMsg.warning(self, APP_NAME, f"'{name}' could harm your computer, so it can't be "
                                "opened from here.\n\nYou can still save it with Save As... if you "
                                "trust the sender.")
            return
        tmp = APP_DIR / "temp"
        tmp.mkdir(exist_ok=True)
        safe = re.sub(r'[\\/:*?"<>|]', "_", name) or "attachment"
        path = tmp / safe
        path.write_bytes(data)
        QDesktopServices.openUrl(QUrl.fromLocalFile(str(path)))

    def save_attachment(self, name, data):
        path, _ = QFileDialog.getSaveFileName(self, "Save Attachment As", str(Path.home() / name))
        if path:
            Path(path).write_bytes(data)

    def save_all_attachments(self, parts):
        folder = QFileDialog.getExistingDirectory(self, "Save Attachments", str(Path.home()))
        if folder:
            for p in parts:
                name = re.sub(r'[\\/:*?"<>|]', "_", p.get_filename() or "attachment")
                (Path(folder) / name).write_bytes(p.get_payload(decode=True) or b"")

    def save_as(self):
        mid = self._single_id()
        if not mid:
            return
        row = self.store.get(mid)
        name = re.sub(r'[\\/:*?"<>|]', "_", row["subject"] or "message")[:80] + ".eml"
        path, _ = QFileDialog.getSaveFileName(self, "Save Message As", str(Path.home() / name),
                                              "Mail (*.eml)")
        if path:
            Path(path).write_bytes(row["raw"])

    def import_eml(self):
        paths, _ = QFileDialog.getOpenFileNames(self, "Import Messages", str(Path.home()), "Mail (*.eml)")
        folder = self.current if self.current not in (None, "__root__", "__search__") else "Inbox"
        for p in paths:
            self.store.add_message(folder, Path(p).read_bytes(), is_read=1)
        if paths:
            self.refresh_after_change()
            self.status_left.setText(f"Imported {len(paths)} message(s) into {folder}.")

    def print_message(self, mid=None):
        mid = mid or self._single_id()
        if not mid:
            return
        if QPrinter is None:
            XPMsg.warning(self, APP_NAME, "Printing isn't available on this system.")
            return
        row = self.store.get(mid)
        m = parse_msg(row["raw"])
        head = "".join(f"<b>{k}:</b> {html.escape(v)}<br>" for k, v in
                       (("From", hdr(m, "From")), ("To", hdr(m, "To")), ("Cc", hdr(m, "Cc")),
                        ("Sent", fmt_date(row["ts"])), ("Subject", hdr(m, "Subject"))) if v)
        doc = QTextDocument()
        doc.setHtml(f"<div style='font-family:Arial'>{head}<hr>{body_html(m)}</div>")
        printer = QPrinter(QPrinter.HighResolution)
        if QPrintDialog(printer, self).exec():
            doc.print_(printer)

    # ---- dialogs
    def open_accounts(self):
        AccountsDialog(self).exec()

    def open_options(self):
        if OptionsDialog(self).exec():
            self.reset_check_timer()
            self.start_chk.setChecked(self.cfg.get("start_in_inbox"))
            if self.cfg.get("theme") != THEME_NAME:
                self.apply_theme(self.cfg.get("theme"))

    def apply_theme(self, name):
        set_theme(name)
        apply_xp_theme(QApplication.instance())
        for w in QApplication.topLevelWidgets():
            if w.isWindow():
                xp_titlebar(w)
        if self.current == "__root__":
            self._render_start_page()

    def accounts_changed(self):
        a = self.cfg.default_account()
        self.band_identity.setText(a.get("display") or a.get("name") if a else "Main Identity")
        self.reset_check_timer()
        if self.current == "__root__":
            self._render_start_page()

    def first_run(self):
        if XPMsg.question(self, f"Welcome to {APP_NAME}",
                                f"Welcome to {APP_NAME}!\n\nWould you like to set up your e-mail "
                                "account now?") == QMessageBox.Yes:
            d = AccountDialog(self)
            if d.exec():
                d.acct["default"] = True
                self.cfg.accounts.append(d.acct)
                self.cfg.save()
                self.accounts_changed()
                self.send_receive()

    def about(self):
        AboutDialog(self).exec()


def play_new_mail_sound():
    if sys.platform == "win32":
        try:
            import winsound
            winsound.PlaySound("MailBeep", winsound.SND_ALIAS | winsound.SND_ASYNC)
            return
        except Exception:
            pass
    QApplication.beep()


# --------------------------------------------------------------------------

def main():
    if "--make-icon" in sys.argv:
        app = QApplication(sys.argv)
        make_pixmap("app", 256).save("express_mail.ico")
        print("Wrote express_mail.ico")
        return
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID("ExpressMail.Classic")
        except Exception:
            pass
    app = QApplication(sys.argv)
    app.setApplicationName(APP_NAME)
    app.setWindowIcon(icon("app"))
    tb_filter = XPTitleBarFilter(app)
    app.installEventFilter(tb_filter)
    cfg = Config()
    global XP_CHROME
    XP_CHROME = bool(cfg.get("xp_titlebars"))
    set_theme(cfg.get("theme"))
    apply_xp_theme(app)
    store = Store(APP_DIR / "mail.db")
    if store.is_empty():
        store.add_message("Inbox", welcome_raw())
    w = MainWindow(cfg, store)
    w.accounts_changed()
    w.show()
    if not cfg.accounts:
        QTimer.singleShot(500, w.first_run)
    sys.exit(app.exec())



# --------------------------------------------------------------------------
# About box (Kincaid Solutions logo)
# --------------------------------------------------------------------------

def logo_pixmap(width):
    """The Kincaid Solutions logo, scaled to `width` (sharp on high-DPI screens)."""
    pm = QPixmap()
    pm.loadFromData(QByteArray.fromBase64(KINCAID_LOGO_PNG.replace("\n", "").encode()), "PNG")
    if pm.isNull():
        return pm
    dpr = QApplication.instance().devicePixelRatio() if QApplication.instance() else 1.0
    pm = pm.scaledToWidth(int(width * dpr), Qt.SmoothTransformation)
    pm.setDevicePixelRatio(dpr)
    return pm


class AboutDialog(QDialog):
    def __init__(self, parent):
        super().__init__(parent)
        xp_frame(self)
        self.setWindowTitle(f"About {APP_NAME}")
        self.setWindowIcon(icon("app"))
        v = QVBoxLayout(self)
        v.setContentsMargins(0, 0, 0, 0)
        v.setSpacing(0)

        banner = QLabel()
        banner.setAlignment(Qt.AlignCenter)
        banner.setPixmap(logo_pixmap(380))
        banner.setStyleSheet("background: #FFFFFF; padding: 18px 24px 14px 24px;")
        v.addWidget(banner)

        strip = QFrame()
        strip.setFixedHeight(5)
        T = THEME
        strip.setStyleSheet(f"background: qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 {T['band'][0]}, "
                            f"stop:0.55 {T['band'][1]}, stop:1 {T['band'][2]});")
        v.addWidget(strip)

        body = QWidget()
        b = QHBoxLayout(body)
        b.setContentsMargins(18, 14, 18, 6)
        b.setSpacing(14)
        pic = QLabel()
        pic.setPixmap(make_pixmap("app", 40))
        b.addWidget(pic, 0, Qt.AlignTop)
        text = QLabel(
            f"<p style='margin:0'><span style='font-size:12pt'><b>{html.escape(APP_NAME)}</b></span><br>"
            f"Version {VERSION}</p>"
            "<p>A modern e-mail program with the look and feel of the Windows XP era.<br>"
            "IMAP / SMTP · Local Folders · Address Book</p>"
            "<p><b>Developed By:</b>&nbsp; Adam Kincaid</p>"
            "<p>Disclaimer: This project was coded using Claude</p>"
            f"<p style='color:#555555'>Your mail is stored in:<br>{html.escape(str(APP_DIR))}</p>")
        text.setWordWrap(True)
        text.setTextInteractionFlags(Qt.TextSelectableByMouse)
        b.addWidget(text, 1)
        v.addWidget(body)

        line = QFrame()
        line.setFrameShape(QFrame.HLine)
        line.setStyleSheet("color: #ACA899; margin: 0 18px;")
        v.addWidget(line)
        row = QHBoxLayout()
        row.setContentsMargins(18, 8, 18, 12)
        row.addStretch()
        ok = QPushButton("OK")
        ok.setDefault(True)
        ok.clicked.connect(self.accept)
        row.addWidget(ok)
        v.addLayout(row)
        self.setFixedWidth(470)


# Kincaid Solutions logo (PNG rendered from kincaid-logo-transparent-for-light-bg.svg)
KINCAID_LOGO_PNG = """
iVBORw0KGgoAAAANSUhEUgAAAvgAAADxCAMAAACJbDMwAAADAFBMVEWm1+EhmaFcYGMWXmklKysgaHCaoKgjmatbzd1b1PRlo92Z
nZqnytbP2+BkaGrW19nM2Opcco9J0embsc5fk6lfqcYza6+j0NYNcZI1x90Xd4UdkKMussZfeJaaut8t3NnFwr4QOUggVt80gdyb
mZvz+voRJztUJgtKerlvlqiSt70JqsmjssspGRUAJ08TMkcAoHlrVTlsc49Y1eSJeGgpr8QA0KJAPTdZq6yc//8AWjYXeoo4x9tI
RT5gZ3F/f/9FuNGQhXq8w74AM5kWRFdAfMVdoauBf4EAAAAOFCgAAAA85v5Nh/4A//9zpf6Nt/5mmv4BAQFK6P4NEycNFCYNEyZa
k/43dv075f7Q5/wNEyeqyf611f7v+v485f4BATk45v4iZbZBff4odNMNEyc85f495f4la8du7P8OFCgNEydC9//G2v6Xw/495f4u
bPzQ9/495f422feu9P9H5/4AAFWDrP6U8f9S/P8KFBU52PBO5v0gXapC5f59//8yhvMFGBg31+8Af/852O97sf4CJykCNzc3+v8a
WaQ0lvY62O+D7v8Fe31G5f0wuMwHJio72PlL2fjm5eQAAP8ZVZszuMs+v/41xdk0yvI1p/YISEpVqv8TR09A5f654+sKZ200x9cn
mKhA5v8DVlcMNToQ5fssprgvuMwZZ3I0xdo5x/okhpQ4t/lk2Ors6+v49/YwxNo3zOQrmKsvt8sBu7sC2f4ol6hWVlYCqaowuc05
2fDKysstp7VHR0coiJRkyNcLWWoBmJgDyuw7PDtA5f7i7f4AAH8rpbg1zOInJyYkWM4khpQzzONPh9LO09cQFxUUU1kZZnEieYgW
WWQReo0Av/852fBVZHWvuMnx8vFj4vW3yO3G19nJ6PINmLEAqv8BudVG/f+jq7gBAQE1xdlD2POyys0ODiYOR1EdYrQsp7o3zOOh
vv7q8fwEOUsQPEQmfIolh5Ytq8Zt2OcIJS4jeocomakrqLstrcIurcFO2Oz39vYANWsKyswA2NhYtsQo1rrcAAABAHRSTlPQG21U
Wx+Tmqbk4Watqg5ey2EVnJ2l9GEcrVpXoZHSCYFS/f8yEJsQ4GzdDGMWBp0HGS1qIWgFYyoHCZfCbYYCDTGGBYn/xH4A/i36/gL+
/v5K/ssvTf7+MPux/f7+TgUV/v7+lI1u/v4Sbv7+/s/+/q4R/hAD/v8GKy3G/ygC/g2NAk3+DwsK/v5u/gmxLS/4Dq4B/hUELQ3+
EgMwbewPFC1UCi4KLU8wS/4u/s9xmY8wF5EGB00LBXCviBQKF9UTBwgMkf4CTU4Q/kuP95ZTMEowLRMEz4qubc3T7dYNAwkrqGJr
8+ojTf1rcv3ZEy0XaxisTFFylC5Oqq4ECAbT1/h53gAANEtJREFUeNrt3QtgE1W+MPDWUqGArou64uPq53Xd/fb57X77vu/7PadN
p4U8ShpKEiAtJIXYhISmYVvSlrRaSku/WlpLsS2FFsTdj/cCF1lAFnCBqwj6ubsu6hXf+6G4vq+695wzM8kkmceZyWTaxvPXdUXC
ZDrzm//8z5lzzuRQJEh8ASOHHAISBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPgkSEwj+Y9fD
+FVqoP9+/RNqd+WxX/3qMSYej8VjsfhVfn4+/NrrHycnjUQ2ZfwIORkkJjD8x6nf/fv/lYp7qcfU7Iib+tLvYPzyl7+E/0sO8N9+
x8S9FMn5JPSH/xj17wsk43fUr1Sk+yeoL/1/oa39JjHKF9zwJer6x0dGRtpPkpNHQteMz4NfU54S6uBD979ZJh/l5bd0dAz1fNbz
7l2ff0ajIOeQhF7wa/g5uaYmgf+CX6oodfDdz2xsbGtrDofDfhB9/r5nCH0SesOvEUj4quDjul9W/vtDjTCqmoF9q9Pp9zu7gPxu
Yp9EpuE/AeCXs8m+XBj+4yrcl8urr1hWXrB+/fpnDx1qrKysqrJbrVan3+ncum8fyfokJiH8iIT7Cl4w7kEYvF6vweD1VVZtRvpB
0PQzTTH8DoeD938kxiWCE/wkpAO/Rgv4kWiC+4rUmF8xH/697OGC9a+AWG+IhRcm/nqrNeAH8ukX6G7ijYQO8MsF4X+JUvDsNhJp
ge4rBGM+P4D7R15Jgm9YBeXbrfXhQOtWIL8JZpeI2eNy2UC4XB4zfCpG8v44hNni4U6CxZ0V8CMawo8Iu58vEMvKf33rrbc++yys
dHjhY4r9ej+sdj5rp9wWW2FC2CbmYc9y9S5TwkkwedxZAr8G9uj8Jj34jpZI9Eo+dUvc/XzxWPbwtDvuAPIPHXqW7x4W+ptgyq93
OltfpClL4gFnjrqFSNSXvS31JBS6sgD+/wGpXrC8h7EME74j0tLS0p/vBu5RBS8dy/548wdvfrhn504AH7RrDUZjQsq3w/6dIbrd
VSgYLpL0dQyL8EkwmSc5/DoEv1wKfp38VqLu/v6R/PwryL1c/GnZDd/Iy3v/zP43D+5sPMTAN8ZTPqryrf5QvqlQJExEvm7hEjsJ
hZashY+6ZTDgt0RBrh88mv/0hVtuwHTf+Xre+TO3nzp4ubHxUAJ8Awu/vnXIJnrIC22kgatLBCmP+EkoNGclfK47csG/ysFv6R85
erH94js7tsnl+z/BKF12wzVFnVsGLuSd2f/xwbdSUn5l1SZQ6oRDX5M45KDEDBKW41fnTMAbrxbwE3rgF/yLJPz2kcGjR4+8c+TI
jtzZEvkeiWeiArivq+vc8tS2M/tPjV1u41K+kYMPUj5w/3qhZJgJSh3CbSqcLOlHOfyiJPhJD50k4bePtA+2A/W5w+CvW/4o4J7j
Hgvofm5RHUz5+Tv2j21/q63Rx5fvZTo0w9KHvNBGVOoQHumTUPhaxq88mYg/1FEKvwjCr2DNVwg8aIXwi0TYt7cf+96R3SCGR0dv
v6V8GQ/88uWlggHcz51bVITkb3t6+OOx022NlSx8I1fkb25+KU/mkIOUT4qdTIdDJvsUejJ+x5ELszbwKxTA724/8L1vHcjdfXj3
6Ojox7dPK1+2HHpfvnx+qXhw7jn4o2Pb29oqvUnw7c0vfU0OPqnyM9+ytcidBFOGOxnMcjsQ71rSCz7dfmDv7NzDh999d7Tjo4/G
fgTcl4pl+ST3cfizAfzTAL6PhW/k4Fs7ZH9i0qU5nl2ZOjW1xhd+kQB86D63p2eop6ejo2Ns7OCfgXu5WLlyfsx9EWrd5g5/tP10
cwr8TXb5Soc0b3UIk+xJ8GQt/PlC8Gn6wN67PuvpYdlf3inrfiWM+Tf8/dw4/LcB/NGO7c18+EYGfvNL/6MQ/0cmkakKW/4k2DI7
ZFAn+MuEBlQKwKfb936W2zM0NNTT0du7/fJOSfcrY8Hke8Y97MjPfxrBb6uK1fgs/Krml/5L4XgnGxIY7DLduaYTfMFBlSnw2w/Q
e+/qG/L3IPbb3zor6n5lQszPmRJ3X4fgD3/UcZrAn7BhkT8JppZsgx/rl0yCPwKK+309/qE+fy9i3yjoPkF8Cfpr/syfxN0z8HeM
dvTCSicBPurHl+/UmYDjA7+Q8N3ZBJ//AGr5b3jwHdG/AVXOXbPgggi9u3q3n247e3ZaTnmFeJov4WL+TF6+B/Bb+gdhwt8F4J/g
HmAR+AS+XvCL4vCXlacOol++fHn5f4rDj0bbj+3uuavP37crvAsUKY1nz/754ZoKIfQliZHkvijaMpK/Y7ijd1fzD6p4bVsGvp2U
OqTU0Qd+BTM6Jxk9jPJYxo9EBq+0f6tnCOT78K5dgH3j2T/nPMzmezHxMOYku6ci0f7Bd4ZHO3aFm6uqKlfx4TMPbgn8ydK4DU5m
+PMrmAE6ieST4Eei0fz23B5Q3YfD4WbovjGnAuR78TSP0INIcU9FQMI/Aip8sB2U8BPbtngZn3Rnku7MdOEvjxX3y1OCK3UikSv9
Rw73DA0h95D9n4H78gph7yz5OSLuo/1H39n9US/YkD2l0qncZA/jPMB6jcjMdGTxAywEv4aDn8p+eSkHPxrtb999uKePS/fTch5+
GLiXQQ9j/nNJ7kHC728/crh3Vzhs37SpclXN0oQSf/Nmq/Uj+eqSLEOe8cjiIQsy8EHxjuAXRUCSzocJP57uH64Qdj8nKVLdUy1X
juYe7gEJ327fdMK3dAEPvu8EnGwebrDJd+qQWVjj3rqdvIPUxOFzPTUMfDi58OLuHlSVs+lewP2clCgTch9tGWnfja4hO6h0vLUL
jAkDFjbD+Vd3k6E6k6DWyXQHwzjAL+XB/05dHSzKc0dh9yN0/2dY5jxcPl9GvYh7Kto/CG4eu8Js07amhl/pwIRvrQ85bWQiynhH
UHYiijvb4PMeSAH4nXWdb19Az1lPM+m+HLqvqVDpPtJy9CIv4RsX1BqXcgl/HZpqbq3v+9ndJOGPf0RMMgk/mN3w4dj5HcOjvduZ
dI/cJ9Y5QuznFAu6hwl/97s94bDVCtyvM9SCEn8p/7EtcO90zpJuWZFO/AnQlZ/5/gWd4M9PUc/A37Jl4MJsNFkKtGpnlpcD+OUL
KuTYI/dPCrgfac/NjSd8UOksXbo0/vQKJXxnoKt1r9TyIlFicvyLHTOVVfBLU+C/PXDh6R2nkHtQ5kD45b+pkGMv4j4SbRnMZQod
pg9/6YIVRkY+N/sKug84X6SviMq3kdlXuoVHwv3JSQ6/PA4/dWxx+X8rGngq/8z+jy+/BdyXM+55+V4QfVlZGXB/rYD7CHB/7Kfw
KZiVSfgrFixFwY3TQfD9Aee+A7SbLCE4cfs0dVlCcJzh551/f/+pgzvPNuaw7svVuqci7pHBSz3wMRhy7zMYUaUD4fMSvj/k3ErT
B8BBF0j6NjJWQd8Qyj8mjy7Fpl7wBSaTrCmf2Zn3/u1vHty585McbumdCsmunDIJ99H+9txL/+T3zwIVPhqetnZBbQy+9wSb8J0g
4dN0E3wvhCVxhWqTi7AfhyauxzY+a7VnGn6pJPy737/65h44v5CJnJh7MfbFxSLu4eC09t1DQ/56q2TCD8CEz70KyPGaBb0ZAr6S
4DUyTmG80n7sJHjMbtTszW74a0rKZ+Zd/WDPnj1cus/5I577uYLuBy8eO4wKfKt9ExydlpDwmXdggYTfBRM+8yKgYGpHA4kJ0NuT
1Rl/DYiSZTPzpn6452bWfcVMzr1okSPunnJfab94eNZdqGW7GbZsUxN+uN7ZGuInfCbroyDgxlc7Ogm6Jh5d4M+vWJ7Cfk0JgD91
6oc3P7+MSffTWPfC6Bn2ou4jV9q/t3eoDxU6wL3PCBL+ihj8eB9+wKn/G84dvMjYN0j+msQ4wJ8Px+Inwl/Dgz/t+eeRfFH3fPbi
7t0jFy/NmuXvAgl/MzMMn5fwvdyrblHL9pmm7HzjYYRZBtVBOmQnCHxm5lVKugexLGdqzqs5UP6yaax7YfUse1H3lHukfe9Ql98/
i0n4XqOhlqvwYaHDdOlYnaHA1n2JhU5GMz2za2aLBzTeUHg8FjP/9zT5AvQNoHEYW+yUaayn+0U4d6jgxLqzcDsTdZvNZosF/MPt
psQOw/jAL2Hhf/PVV3OA/Jybofs5qt1H+tuPvTjkd8Z6dAzGBTVJLdtw2O/vG3rx0rHZupWSbrPHljoUy+SymLXqqXaYPS6xwV4m
G9NJkv6XwNsICnM8wH+agN1gDrPFlXjITTZwuN3jnvHj2R7Bf/7OV4H853P2MO6Tx1/iuo9G8w9cmhVwsoPT4ETbFWzCj3dlvtQQ
+tm9ut5LXeLjD4HJ9JOb2+KSG9QOLjKH8rQPhVvAfQreqOALaJkbSfKmk+4s498lJp4EhA6DnvDXrEmGDzL+q69Ou+NmIfeJ6iXc
U98dOQYLHZTwq1Chs5Rr2cbefPXS03ffffd771kwQ9ClWcHHLXLzvGzmNHObS37aKjMKw6wkNVsEjMtcXCCnujEvLbdFUSi4Ybnl
DrjLrG/GXxODn8yeg3/zVOR+jmr30f5j3+ph3W9mFg2siSd8pmUbbviasrMplGRN2HNXzDaM71BLH+RWh8Wm5IfxOLCzvqdQVdjw
bi1mZVs1499dcfbRMh7w15SmuEfw77wp1X1ZWQr74hJJ9y8C91ZY4G9iC50VS9cmFDoyL3zDmYXloGy4H3dhfovKIXERj0mhS5MH
N+urhI/qCfmmS2bgm3GPNz/V6AY/1T2E/82pU28SdV+M497x3cFLL/q7/AErW+DDQqdm7dq1gD67JD6APyukQcbHhG/BZ6lqHKLF
pIalJdPwUdPFoT98t0vBFuOpJpPwi5LhJ00gX/b8/0p1L6BeMt+3tB/7zB9gCp1NlVyhsxbKR4PTkHur/2dT9IKvjI7i+V5mm1qV
5ozDh7cWt87wLSoTgI7wU1YLWZYj7r5Mwj3/W1pGLh3f1xXryfQyhQ50v5ZdWQE+su3y36sXfJdCKsoWqHWkA9OTefgyVZXm8N02
tUch4/CXI/ilAu4B/L+96Qa++7Iyhfne0XL0GKxznPX1XA++oXZBTW0tSPlsjw4zOK3vXo8+8F2KT4RLj3SPPb0sbfiS9ZvW8C1q
9s+lC/wSFr7QomjLvvm3wu6Li3Hz/XcP7N3aFWDy/Sa2wF9QC2OpIT7tKuCcRekD36P6RFDa39bVtCk0gC/RaNcYvtouqAgVzDD8
6yB8NNtWCH7FzJy4e5FsL+1+sH3vZ7MC8YYtKvBXQPdrucUymdknQ/rAVycTt87XAqVFD/iFttf0gO9SvXv6ZHz0flpB+Fx9X1Ym
yr645A8zROocyvFp+4vH/U6mJ5Pp0DGuQIVObW28J9MKpxu+qAt8c4Y0Ms14lyYmPXrAF/uRtITvTqPsc+kBf7lIxp8zpwLL/f8W
y/fA/d7j/kAr455p2Nay7uOPbOvhYOTj39IFvknticBYntlh04ikRxf4wvK1hG9L7yBkuh9fDD5a5BvH/TVi+Z76dHAvaNg6+R06
axcwhQ5b4DMNWzgmc68e8NWjkV/MRzP3MouUaQZfUL528NM9HmZ3xuCjd2AtE4Yv1JEjwH6RhPuWltkHPufcb96E3C9NKPC5ldOc
zn30sYzDP6m60MEqdrRzL53ztYMv9DNpBT9IpVv3mTKb8a8ThC/MvrhYzj2V2LCNu2cbtsA9v8BHDVvQ8g3QNN2eafjB9GxKL4rt
oFyFWoZFF/gCbjXL+Onvpi1z8OsA/AoB+GrdJ+b7Ywc+hx2Z1rj7pIbtJljohNnJJyOZhu9IK+HLLZLqKdQ2XtPlm1LfW6gN/GD6
/bqK0oNG8AXdFytzj/L9Vn+IPzINuI8X+GzD1uoMdG2l6RfoYObhp1mMuLV70o/x40V1ucRsGcr47sIJDD9SV9cJ4ZcmwheYZ6LC
veO/H/jxcc59Fc89+Iv35MoK6vut+5jZ5Zmu8dPFKZryT1Juk+Yn1SW2OKW29xZPZuDbJiz8CBVx15lj8EtLS5Pcl0lXORB+6cwn
xR9cHfj8eFfIGeC7BwX+ChBrDfF3QDhbUYGvC/y0W1tuXRq2cqY0Lqrc2sMPal74aQc/Eom43Z2dWxj4aNKhkuKegV9cilZEFuzA
P3AXrHMC9fEHtrWs+1pmvUD40h+4fFRgH7eaSIbhp5+VLXoV+JLXmSejdxZNMr4+hY4a+MB9NNq5ZcvbdQnw5+Cn++JFixbNKy69
NgY/Id9/euzF4wHW/abKdcnuY+sFJqwmkmH46Te3bPoWtCKllSejdxZN4LsmKvxopCUajW55e2CgE8IvZeHjFzmQPZI//1qhhP/p
MabOqWffe8K4X5DkHq6i4+ctm5Zh+BqUI47M9Fgra01rDd+mMfyg9i19reBHI9GWlpYrAwMDeVOuq5jDwhfM9mVi2R65nwfkz0jt
yPz0xzDftybVOcj9CmN8zpXViZYLjC2blmH4mhxohx49OvEqRJe6yqxxxg/aJij8lmhLtL+/f+Cpp57Kez0FviL3cfkJ+f7F436e
e2OCeyNvucBZrfzlAjML36yJxJMZHaqAVUh4tL++gprCtxROTPjBlv6R/pGjRy9c2HY+Ly8ZvkL38+aV/WFGgvuW734PuA+k1Dmo
wI934EP3oQT3mYXv0sKLQHvTkcnzLPgea83hJzyT1gC+bWLCPzky2D94dHBwG4jz7wP4ZexKUgLuy+Tdz5s3B8qPb/+77ZeAe3/M
vTHF/abNvBdA0Pwp2rzQPOPbMpSCM5jwhTt2PJnzA+GbFJ0F83gmfEXwT7aDGBzMb8/Pn33b+1dvy+Hgl6jK9yDuA/KpothKIoO5
L8KJJ+F4vl/Bd8+MyKyHHZl9+44nLIscZdZUhYExlFshfJNJayLKz7PNgxZh8rhsaXxfBuAntCXcvJNgUQNfYVPf5mKPis2UUfiA
/eyj77xz8cjs3B1nzlydmgC/DK8bM8E9lD/zn2OFztFje3u6/OHYS0+S3K9KeP/DC03q5+4ohJ+x5ibuVzLrOXG6PHh/zKYIfnxN
WhuzrqD6qhH3ok5zlJsrYSm21zy2jMGn2/cey30n98iRHTt23H7m9g948MuwOjJT3c+7776S665nHg9ERy5e6hnyW9k18IXcx150
BQfodI8jfJB/0eKqFgWH26T2PHMrh8RfroC39o5ZDD7iDVd3ZvIls0wsjEhsfeSI24y5nJtZQ/gKbkgediReMP7GCbMrM/Bp+sDe
w7m7D+cOg9i//4MPE+Cryvcx+RFQrPzNYO7h2Ns84+5rVtTUJLrvgs1aqWXwMww/cXUZ/MPtVjca2SOwdh/WxDyBgflutA4y7iqz
WIs5iY1CUgMfu2CB890dyY8AlC1TgQ0fYNv7+eHcw4d3Dw+Pnjr15ocfTn14fgy+unwP3d83b+V134evbx5p3x17bXnMPYCf5N4f
QP053dR4wXc5mM+jdKNkVZDkE403DsKiekqqDWPGI7yLBMWGB2M1QlwiS2qqgG9WjDaNewYu/G6A7bO7cg+/2zM6Ct3vuWPqX3jw
52C6F4AP5H/pCaqlv/3I4aFexr0Xuq8RdO9E7qVfe5JR+JbUP4l5uJMfYZnV/CEF2dGU9vr5OP2ttqBGpY4DV63kKipmk7bwYZI9
/k+Bu959t6ejo2Ps4J49d/zlLyIZX1G+Z+V/58rRd3Z/1Lsr3Gzn5hmKuHfK5fvMwjerTzSeJMMudeUK/mVj0eDVLB61l5fyjP8E
3hmQuZ5xxxMqgE/3bRgaQu4h/L/8WgS+wnwPY1HpLf3bdgx39Iab2fUUJN3LveYqg/DNaSwC40qqhk041UowjfmKHir9iJpUHhLl
8M1auMeWjwW/G7m/y9831Nfb0bt97ODOPdN+PV0YPn67Nub+vvuK77xl2/Box+nmtkqfgPsTifle7mRlDr5HvY+UmhvnPEudZIea
DlSlgTE8forwfUU5fEthOqlH6QWEBR8VOl2BPr/f39vbu/3yzp3Tfi0Cv1hxocPJz/14e3NbIxyWZqjluTfGVxJpDfj3gXxPjRt8
U0swjaNtcyitaD2a/5jKw6yyoFIO34XnVa58wxwIggO/m26iaX/I6fT7w7t2bT99duetvxaBr9L9vPuKc24ZOw3dG9G6Uax7I9+9
P3mcgu7wLaKVRxDjjyfcpE/ifJ9bMhfLX2sRPWodj1aljgmrXMQJlzbwUaHj7ws4/U7g/vTptrNnfyECX6X7++CAtZwfvNXIrRPI
c8+Mz6kXGJ+jO3xTemkmsTp1mNI9yxFT+mUBRseOSyf4jsI0az9ls3sw4MPHpMdDgVaY8GcB941nP/kFlD81Jxm+2nwPY/X0X3zC
dGMuWIDcL2DHITMTbP2BLhr3teWZgu9Js03lVlgbmSUXJcFo3moC36Pu8lQMH6c0l16mRdG8XXn4yFso4Gx1Oq3hcHNzYyPj/i8p
8FW1a1n2qx94oABCX5rsnl1QgWnW0tR4wpd2pPDPY9whHGmSLLQoQx5UNV1RK/gYWLEbLa9pAL8bJnw/qO+Beytw39Y47RcQfsFU
LPjcPMOSRTLuH3p0PezOWSDkHpY5W7HdZwy+O70e78Qz7cGodGTSm9kmExjwg8lXl8OdGN/RBz7WAA68hI+XheTgozzb1eUPBJzO
sBW6byxA8O+YOnVmInwp96U3rJR1j5q1XNQaWPdwvbRACC6gI9d9n2n4Mj3ICs+0q1DjfK2ut5IZTWy2eODbnk1CUagT/DQb+0q/
HQc+KPCdzDr10P0nv4fwp3344e3XJcAXL3SA+3+75s6V4u4feOChR5hmLRdw/Rz+egr4dU7m4NvS7T42K+vDcGTUvIMdteZx2dKb
bqBVqSMP34b/06W9aCyT8EOgznFa68N2extwD+FP23PH1NsS4Eu6v3bKy39/55wU97HyHrg3cM1aWOmw006q2O6cwL7jGN33kwu+
fEEbyTB7tzld81rCx+jl8uAPwZDvapCGD3syn/FD9hC+3V7V2IjcF+zZ8+HV83H4xdLun5vy8ssvX/OHOfclwhcs7xn3RmadwLDV
GnDG10sbb/hB7eA7tMxvKgoct0WrhU00go/RBamkk8qWHnw0QgfO/oburfa2ysp1bMLf88HVvOvmF69k4Uu4X8S4f/nlf5hffJ+4
+3h5zz62amtuDodhvt+6TxH7yQHfrBaUJvLNLu0W7NQIvvwBUTDaFKOpLAkfPbpqdbIFPhwwzLj/ZOeeN6++/7oM/Lj7uQj+3Gv/
BOQnuF8tUN4z3TmNyH3Y72fWQ+7+4sH3UJkq8i2aLlOrG3ybkkrOkw58VGH4QwHYo8O4P7Hq90B+wdmdBz84kycDn+eei2tLFwmn
+3h5D7tzDIZD0P2uXeG+vq7jexXm+8kBH6fbwTEJ2OsI34V/QLSAHwr4na2o0LHDQmfVqt8XwIS///28KSz8lYLwWfcrZ8bdA/kr
5/HTPed+bYz9AtisNa5rfGv79t6OjqGens/27j2g0D2BL9n3X1g4AeEHsW6BOmV85L4VDtFxhpk3NJxYBeL3n4CEf+rM++ffY+Cv
XLmyRNx9zk947uc+eSOSP0+szEHl/SPTC34wNtaR+9G7uy8dO3Zs5CT1hYRvzgD7kxlYm1kj+Ap63jMMv5tt2frZlm0VSPgQfkHj
2csf7z9zPq/zXyH8lYLw2XEKK3OumZsQU56bI1HmoPL+kYceKJv2g9zR4SNHLl78Xv+nyk/vxIcfHB/47kwsoaIJfMcEgs904QdQ
Fz7bsoXuV33SeHbs1P7bzr9eB+CXCMNnH9iu/EOS+7lzr7kTdWoy6T6xFxM9rV3/6EMPrF5cPPOns3cMDo6MtEQpAl+zMsdUOJnh
m/WD/4wfdmVy7xavRO7XNTZeHjt1ZtuFgSIIf6UQfDbfl6S6fxLIL+On+xWJ5f36Rx9YvXrxkiXFN/60/+iVqLrp0gS+SooEPuu+
rysAxwtY4bMrttBZ1djYNvbx/h3bnhKHz+b7VPdPPvnelPduurMMpvvkMqcGLgL+CEz3wP2S35678Xp3VOWzSwJfR/fZBp/pwm9l
KnyU8E+whU7j6bFTw09vGwDwl7Pw5wi5nxNzz77+Ye6T77035fW8vJsKpj/w6CPMFMMFNUnlPev+t7+d/u3H1Z5iAl/V7hH4vK7M
VtiVabXGEj4odNq2j43uyL8wsEUEPjfxBL3qh/dew7pOxD7vtqnTCh5hy5yampr44BymvF+M2P/2r4H872QtfP17ddymSQ/fohd8
WOH7Q/6EhL+use309o5hUOm8LQJ/URJ8jr25c8vreefzbrs69cM7XjEyKymgYNI9KHNAeT+PTffAPZT/BYcf1BB+5pbEzS74oNJ5
Bg5W8DtTEv7p7bmw0tnSycEvEYI/b17pjLj7urrOLQN558/fdvWDD+/4u/XMCx9i8NHYe1jmxNwvgbF4+owvMnxNH2Bl9A0UOvXj
6/EAi5lfzo5O4yf8yrbm7R2jO2ZfiMMvSYAfn2mI4MfZP7Ut77YzH7y559ZnYXW/dEXMfWKZg8QzseQelfLJWB21hQ634Dw/XHrA
13jIAqV2kBo7DD+W8Nk+/HWVjQz8bRfehvBLU+DzZthC+Gxx3wnYP31m//439+xE7OPpvqYGlTnrH2J6MWPoOflfJfC1GIaM9cDW
ZYmoEazjILWTGpZ2EvDZCebW+EPbdZVVzc29HcO5257a0mlm4KN3OwvNLC+dUTSXcf/2wLand+w/9aODO5PTPVopLV7mLE6KJedu
/GqWwnerLSFUJXycZK92ofuJOCxZ9UQU1LR1Mk9t63kJH8AP9340/HT+gCD8hBUVSmcw7LcMXMgH7McOXm58Fi4XBdP9ioR0j8oc
oP6ee7SRPxngf11eonaVDtZq39T4wseoxixaXuqC8NEoHS7hxx9eoYS/q2N0+OkLA511dSnwFyXDr4PpHlQ5w6fGtl9uPGRg0/0K
zj2aWcuk+8WLQa2T4n4JkP/DrIRPKVyGJ8NdOi5qvOFHcKYeanipi8FnRisEEpq2lUylA3vx3+bgl8ThJ60cBeB31nWidP/x2FuN
h7xMdY9eWbuCS/fM2Jx5kP09Qu6h/OuzEn66y/jA8MitL/KaBuWzTvDTW8lOMQFB+OzwNCeT8fmVTjOodDqGd+SDEj8FfvKKaRD+
FlDdgyrnclujF1U5S1dwUbNiLTdGAbifJ5Du2S4eIP/72Qjfo0GCk93l1/C69iSvMX3gY62rg13rKKmbkuAfD4Vi4zLZSucEqnQg
/G0DW8zJ8FNWCgTwX887f2b/x5ffilU5PPeQvbGAS/fi7oH8b389C+Fb0krDzD7LnV7UHAzKHw8bNQHgY/Q82fCe6WGtlywAn2am
HHbBx1fh+LhMpmm7qzd3+J3BfpDw+fAXCSwVWDrjvfPvnzkF2rSJVc4K7jWGhvV/VzB99bwlQtU9z71y+ZMCPsbYGbkiX3YTzCKE
T9jSyKRB3ZYQxHnGhvk022FTDf8ZvzOW8dkSH8C32wH80d0Xj6bCT10is3TG6+/vf/PgWZY9L92vqIVlj+HZO6ZOnV4m737J4nPf
zj74Dpy7sSO9p5M2Zv2cdK4w+RJEK/hYfa7aPacWgM88tg3EF9OJ9enYQcbvGD3SPtIShfD/pXQRB19gadjSa2/74ODOQ8wTq6VJ
6R6wv3XP1Kt537izeLGc+yULFQ5emAzwT2qwchjG6n4OnB2T6jjVDz7W+vgejSp8cfitAYES3x4GbdvDovD57FevXjPt9j0Me8PS
WhAce9SoNTy7844Prubl3X3NnWWy7hcC+V/NMvhYNa05zYHGHrzP2dJqQWsGH2uFKzNGhY/5ahXBUgfOtU3sxWcqHQR/sB/AL5KC
DxdQKJh2K3pgZTCura2Nya9l2N+680cfXD2f9/rdT14zvVgaPnC/8A1F8idFqYP18qA0e+fNeARdaaVPjeAH8QbS2SKaFDpi8J+B
8EHGrwcZf3MS/N1i8Hnq4RSrglUGtsrhArBHjVrDobMH39x/G3A/5b0n5365ZLVcwofyb/5qlsHHubVLVfkY59etAXxzoV4ZH2+q
jI2S6ezCHIgqAt8fL3WqOPhVCH7P7ouD/VEW/jwW/ry4e5Y9M8WKz74WsEfp3tv41kG0TMPd0P3cuTeV3COd71n5/5xl8F1p3dkx
Clkb5hMD28l0xrdpBt+BN4TUlWZXl3SpA+Azs22t9k0Q/joGvjXc+y6C706BH1Mvwr62linuvYfa3hoD7rc9NdBprmOWmZojk+9Z
+T/MLvg4p0h0YFYEo8fOgwlfcvSXTS/4mLU5OA9uLSYepMLvFoDvXRfL+O8KZnxesmeXDYHs14JIZI8Wxdw+hqZwddahmbhz5z6Z
IF+QvSL5kwQ+VucDfH+9QLmDtUKOmfmTac1yVL24rYpvxU3WIscEnJ0n8BfMkocPSh3funjG70nI+HNi8OPJnmMP3ddy8pni3lfZ
1ny6t2M0N59zX4SWmbq2TNY9kP+Vm7+fRfCDmBlO6OkS1vqXXCJPY24TThbWDj6FPS/YJZz0lSwcJN64ha+15eDzMv63Dl9qH2kx
J8AviyX7R9cj9kbIHiV8lPPXssV95aZm9CQg952jV6J13OILUP6NxbLuF76x8D9/4+vZA/8kzivK0Pcm0zfjXTHcjCWlLyLlX5vm
Qj3h4+drk4fZZQcK9hsVzSsWa9wya4PXoyFqPq+XydcnNsFhyXCU2sCWTl6pU5aU7AF7FIz7GHt05ezqAFfOUbRCGk/+NdPPLZFx
jy9/kpQ6+DPATS6Lm4oG0ZvZzB7cP2XGryDEZnvhtDc1hO9WItdmcceW2Qs6zB6Fy0iING5bnVv9qDMTuTdwAUuV5u2s/Dj86Tz1
cfasfJa9D77YJxwO9/RA90xvbIL8e5Ykwl+YGvcD+dkEX8kUcJMJjjNWcHZtSkpni9rRvZrCpxS+pcXm8ng8Fo+q13iJPbnd6gww
s22rKr1x+FB+2+ntcEGppwbqZpauhuzXrJkuqB7CX7qUbdMy7y8MO/t6Ll3sj3BPIZLlSyb8n//850D+jCyC78jYYjfozAbVPMFX
7FBL+OZC3UJkWDJwH0CFzqZYwjcaOfnbx07tv/2283kz16wuWTO9oOAVI/cJUfZt9mbIPtA3tHdwhHdb5cn/8vTFfPkLheDjyZ8s
8IOZXPWD93porNoINXAdQe5oUNhL6WsJP4PL/+Bk/KZngPwAm/HjlQ4jHxQtjY1vXT548OCeXxQ8+gqHPkU9CGO8B7M5HLaCa2nr
5z8+MJLwk/Lk/9X0xdL5npX/1azJ+FjjZ1WGR9GoIFQzR1S0oDWGbx7vjE/7Q/GmbZy2QSSMQuyZ34Jv9TkN2rT+gB9utz35R+XJ
v+ncYul8jyl/8sDP3ImOJ3z8+wpoQ5vNbtB+Nls8+FekpvA1Tvku5fCdrYFk+CLyjSiWJsmPsUcv9ekd6hk6/rngy6z4nZo3nZN1
D+X/1Q+zBj7lynRCoxSum4nxLvNMwtc0E5jMyuFvbW1Ngc8aT/xVPFJqnGcP7Tw4NvZRx+i77x44cEnsXVYC8qXc//x+IP/6rIHv
zox7m9Zp1KQTfErLlxV5lMJvgjW+018PXwAE5Cdnd7Hg1CP2618p2HPwzVP7h4dzj+Tmtg+OiL6xkyf/Jzefk3cP5X8/W+BnqH2b
+FVT0r+QbHrBp7Tr6TJFFMLvpl+A/Trc/KtKL6b8uHrD+kceKph2++1ndjyd3z54tH8kKjWJLqFTc/FCWff3PygtfzLBP5mRYidp
DEIkbUwWveAHNSx2PJRC+EyHJlwsGT7Cgj35mCmfK4PQYjlrvnE+b9uFgf7+aERu8oCM/GT39z/44MIvfz1LMn4mVq63JT6IDaZd
P5jc+mV8zYodU0QVfEC/K7ZkLJ58A5fs4Vo580pmdA5s6YxGKYwX+vDln1ssl+9hSMmfXPC179lJHXqT7sXlofSDHwxq1LNjppTD
Zxu4XUzOt2/CkM+pf5RhP+++khlFnUW4b7HiP8g6t+QNmXzPyP9OlsDXvMw3a/0VJneLjhlfo3ugi2pRA59ixy04Z8HZh1UnfBLw
ud+Kq4dvcS6Ba2dSyuAzD7LOLXxDuCOT5x7Kzxb4lLavXRacr2hLb4sRPeFrcg8Etz2HKviI/j7eCvmCTdz4f0tUD2IOXC2ZUiH/
yZvOCVf5Ce4ffPAr/zVb4GvawLUINhnT6Ta1UZSuGV8T+WaZ7UjAj/XuBOL0BZ/drgdlPVwLMGb+r2Eog8+XP+Wm//nG/W+8cX9K
PMiPr4jKn3zwNZQvNsLYkpYhneGnX/0xQ/RUwudauU5mnfz65k0n1sG8X81k+2om8xcUFKxB07DY4F4SsVIZ/ET559h5KV9hYqFQ
fGWhiPxJCF8z+Rb1s8alLiW94acr3yN7TmTgc6OUW/0g9Xf5/X3hcHNzW1tjY+PZnQenzQRx443PPffctf+WENfeCOMaRe4T5f8V
jP/Hj3+A/7iGiS9zkT3wNarzLdpfWwi27vDTk++iNIDP+afo9tmfDgr3xCQFR1gZ/IQWrljgbHlSwteib8dkTm8oh+BPHRkf+Iom
0IrtkhbwmRtmS0vU7XZHpN3HfFKU9vIxrqrJCT+dM83uoNzLg1TIZ9fyGAf46sdsuyjN4WMyVZfweZssSsf9ZIVPRdIr9DEWVFVc
T3GD3cYDvtryz0PpBL9IM/e8bRbJuc9C+JjLhojsnRnn+Cq8q7ieGFf4am6CJguVafgiSouK0oDP26Zk4yFL4VMOlW1cE+6L0dxK
7ipxQ+MEX/nxSFxmLUPw+UoFgqIoLbaZSl5u62pefTNB4CuY8pdwd1fwhkSzTcU9ZLzgKzweJgv2OUkLPqW9e9nLKWO9OqYJAd+h
nL4JrisWpDSmDw3FN9piUpJFNITvUHClmjwRSif4VAbc48mXbBOZZEIwSblU/Sn+0Cq5MGPLVLA6ksmj4n24sl+QvHqbQ/zoeMSa
KzJhM+PvrkvlgTBjnIwcbZFSaUU67FWHg5ogAXbEYXFhLY/pMqvccakvsHnM1AQLt0VmzSibxaHyDOZoiFSLH1Vv9hMuHHJLHdg8
lkg6XzACF1NI4mQCGzVPzOPhFr1U4eoQ6rebo5VSDX/WL656Nns5zILL44Gyy2N2pHmXYv5oFC4mYvHApfjg2iLMlRScgMcD7pPD
bYHHwxQ/DvBCRTsdHB/4JDJYeiGayGbMJw+D5sWdY6IfD+DfzIQ7osE+E/gT/HRPDp2ZPx4OjQ8EgT+hzzaIYDDIWw2ehEZB4JMg
8EmQIPBJkCDwSZAg8EmQIPBJkCDwSZAg8EmQIPBJkCDwSZAg8EmQIPBJkCDwSZAg8EmQIPBJkCDwSZAg8EmQIPBJkCDwSZAg8EkQ
+CRIEPgkSBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPgkSBD4JEgQ+CRIEPiKomlDX19riCYnmMQXCX4DJ56eoPRp
ulv+IxS5bgl8ZawoylpVVVllt1IED4kvCvxumrL6DNUgjAafVSP5NOUzGAxeJ9WkydYC/la573P6DFV0AxFK4GOX91SVodro9fl8
XmDfro38bgi/2qAJfJoK+Lx2aqP0Z+zV8OvIDYvAx4yN1GZDtdfupKnWVjuwWq8RHqffrhl8p7e6igpJX71Wg9HX2k3gE/iYqhr6
fNWgJGHCaqj23StbL9B0aCNGM1hL+OBOFJL5mNXul79m6Qaw6/jHpgHrszS9sYEm8Cdbwq83gHTaSsPoo6qqDVbpooKi2d+WOdch
WgY+vTH+PQ1SPamhEMz4G7s2bpQw27CBkm+Zs7tOyzJtAvvTtJH5rPzlwRzIJgJ/MkUIJmZrE5NON9Ag5dspyYYkOM2tVhA0JX2B
NGiW8YEtL9grLW4dVADuOiWz69zP6bRanbJXE80cD3+Wd4hlKXw2a4GioqrqJakzCCocZ6XXAHtsKv2S1YcM/Caq3ufrQl9FU6FK
n3jjtbvSBxrKsPHtE+t0QltAv90guetWdterpIsi0FIGmwr74Ie9Mq19mvKjjXo16xAj8HWCbzUaNlP+jU145SzsAqo2eL3gn9Im
ZOADhcZqKws/ABuvG8Q+aag2GgxGGCDvNwhvrNVbXQ0b5hKX4r38XbdSL0j9kJXVdrB7wHN1tbFS8mqirF60UfBpezbLz77GLQ0K
aKZx29AaAnW+ZP0boqqMALzV6bTavdKnWh6+wYAFnwKFhNdYBWsUWFCIbM5qrYLbC0nsT2V1tQ/suh98UnrXIfzNBmNVvRX8lEap
djVNgyvOW+93Out98RsngT9Jah1guao+4GTbpJItYbvRWMnqa4WnWpyPdvAxa3yrJPwG2G6vZH8Bvs8QEN91AN/gNYSZrQLY/n+k
xYsieBDQ4YA/QyuBP4lyPlcC+HyVm51Ut9Qnwd3BF6I2NDQ1NWyAfHy0aLemdvBDG3F6dUJ2KfjMrlMbQw1NNLPrlfQLUhkf3BJa
G+gGPyM7JHE5+ahWuqlpFmWftjmLa51sHKvThBp91WjQAqjbmyQ+aDfGezv7GBMNGYeP8wALtlWk4VfxdrYV/kr8MS+E73U2wV3f
yPRzbZCA722FXZobNlBZHdk6SA3U7PaqSjhkp1J8iGYIgqDiIzlD0CM9KeA3UD6Qmrl9bWI4N0jBZ65v1Gy2S1xP9QZjZQBtN7sH
CmVjqUNT9AauieiDT7MaRHFBPTxMoGAQlT3R4MPihtuZbmqDt3qTdMZnjgm7byHxmyBo7Rt8zMjWJgJ/ksEH/wht2BBqQsS8op3c
ISQ99psbaR//lxMZPk0l3p1o8JOckIZPYcFHff6oTDRIP0Ug8Cd0tFJ2g3hXzQaQ8SvjhdDGxOtgQmf8JhpsIr7rNC1VpSmC30B1
O0GZ6ENdpKQ7c7IE4Mk9QOWKX/EubqbGj59zZCKNxq3Rin6bpvwZh78xocanaaeherNMjY8Hn+J+z+qr9gayt1sn2+BvhOPYrbGe
vRAtlfEbmHE9dPzuYBQf0YYFnymzIENZ+HSaNX5VtSHApfw+UJlLPINQAJ/Zf7oh5Ic/T332lvnZBh+gMoB6hRmrS7fC5qt43uI+
jBiEmkLws2r78cGFw7Wj++BjMUn4fgSflhoKLdudWQ93vZVmLlnYqd/XQKULH+yZb5oVjTKlW/2GaivJ+JNIPnpYA/4FZfIqqV4d
OGKhGhClmppgJ3el0SAxL0oOPk2heQBNTdC1dKlDJ/YmqYGPRizAn5OGXxjyST2VUgC/G2UCeOzgY0CDn8CfPEU+rNQNldYu8O/O
zaCJ5g39o/iz/AY4TqHSCv+93meUaNpCaZsl4TfA2sALKDbYV3mrJIcsbEDDDayBQJd4ES0Hn25wxnbd7oOXr/RYHR9WqbMR7llV
H7xt2cElcC9p3E6mlF8PxxcavF6vwVBt9EnOW+2mQpXGajhG2As+K1l3y8FHZTccKeE1VtvtkvBpGlxvcKykRL9JiLJLD1KDZUk1
t+sGyfZqQsbvkoJP02ijzHxlnzOLe/KzcqyOv2odM2LB4LNTcsPP+f3W0p+0Fvj8UjOwQHUABxNXr7JT9gLJMb2gOKnyScOH44Pl
BhtTdnCRwV2vtMqMx68qYG9mcKI72LcXpA6elxnsUeUnw5InVwCbXXDEgt1q3Sg/4aiJ2gA+bIfzmGRu7Bs2BCQ31g3UgE1Z+6im
1j6/zFVEbXTCkKry/U7pHYKTaNCuB2R3vasv9k20s69Ves+60EazfApWdo7VaeWV07IRSvkX1RHC3hCtyRiwDbGCX8ODx+19iEw9
nIT04YIC4G8a98NYn6UxFj1oYFYywFgisImmpTeIs0cNeLvO/ybZT7MbpSgCnwQJAp8ECQKfBAkCnwQJAp8ECQKfBImJFf8Bq/DV
Fdx4eCsAAAAASUVORK5CYII=
"""


if __name__ == "__main__":
    main()
