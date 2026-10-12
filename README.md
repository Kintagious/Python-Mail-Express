# Python Mail Express

A modern e-mail program for Windows 11 with the look and feel of Outlook Express 6 on Windows XP.

<img width="1469" height="884" alt="Screenshot 2026-10-12 172958" src="https://github.com/user-attachments/assets/fe3fb270-67e5-4fa4-b57f-a44801ce6f49" />

<img width="1469" height="884" alt="Screenshot 2026-10-12 173328" src="https://github.com/user-attachments/assets/6084f0dc-9661-4558-8f1f-fedc0b0c9f57" />

<img width="430" height="320" alt="Screenshot 2026-10-12 173030" src="https://github.com/user-attachments/assets/e32e447e-8015-4a7d-a34e-437ea4fc083f" />

## Run it

1. Install Python 3.10 or newer from python.org (tick **Add python.exe to PATH**).
2. Put all the files in one folder and double-click **run.bat**.

To make a standalone `ExpressMail.exe`, double-click **build.bat** instead. The program ends up in the `dist` folder.

## First start

You'll be asked to set up an account. Pick your provider from the list and the server settings fill in for you.

- **Gmail:** click **Sign in with Google**. Your browser opens, you sign in, and you're done. No password is stored, only a sign-in token kept in Windows Credential Manager.
  - The very first time, Express Mail walks you through a one-time setup that registers it with Google (free, about 10 minutes). Google requires every program to be registered before it can offer "Sign in with Google".
  - Publish the app in that setup (step 3). If you leave it in *Testing*, Google signs you out every 7 days.
  - Google will say it *hasn't verified this app*. That's expected for your own app: click **Advanced**, then **Go to Express Mail**.
  - Prefer the old way? Click **Use an app password instead**.
- **Yahoo, iCloud, AOL** need an *app password*, made in your account's security settings.
- **Outlook.com / Hotmail** aren't supported yet.
- Use **Test Settings** in the account window to check everything before you save.

## What's in it

- The classic layout: Folders and Contacts on the left, message list, preview pane, the blue folder band, the start page and the Send/Recv progress window
- Local Folders: Inbox, Outbox, Sent Items, Deleted Items, Drafts, plus folders you make yourself
- Create Mail with rich text (fonts, bold/italic/underline, colors, lists, alignment), attachments, priority, Cc/Bcc
- Reply, Reply All and Forward with the "----- Original Message -----" block
- Address Book, with name completion in the To/Cc boxes
- Flags, mark read/unread, Find, Print, save as .eml, import .eml
- Checks for mail every 30 minutes (change it in Tools > Options), new-mail sound and tray notification
- XP Luna styling, including a blue Windows 11 title bar

## Good to know

- Mail is **copied** to your PC and left on the server. Deleting here does not delete from the server.
- Only the Inbox is downloaded (the newest 300 messages the first time; change it in Options).
- Pictures from the internet are never loaded, and dangerous attachments (.exe, .vbs, .js...) can only be saved, not opened.
- Your mail lives in `%APPDATA%\ExpressMail` (mail.db and config.json). Passwords go in Windows Credential Manager.
- Heavily designed newsletter e-mails may look plain, since the viewer is a simple HTML renderer rather than a full web browser.
- To rename the program, change `APP_NAME` at the top of `express_mail.py`.
