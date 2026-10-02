# trackED
Audio timing track editor.  Can be used to (help) create timing tracks for Audacity, xLights, etc.

# Status
UNDER CONSTRUCTION

# License
This project is licensed under the Community Source License, Version 1.0.
This is a source-available license and is not an OSI-approved Open Source license.  See LICENSE.md.

## Known limitations

### Composed input (input methods) is off by default
trackED tells Tk not to use the desktop's X input method (XIM -- e.g. ibus,
fcitx). With an input method active, Tk talks to it synchronously for every
text field, and a timing track has several fields per card: with ibus, opening
or switching a track of ~70 cards kept the app waiting for seconds.

With it off, plain typing works, but anything the input method composes does
not -- East Asian and other IME input, and on some desktops accented letters
typed with dead keys or the Compose key. If you need those, turn on
**Preferences > "Use the desktop's input method (IME, e.g. ibus) in text
fields"** and restart trackED (expect slower track switching with many cards).

## Tests

    python3 tests.py

Headless (fake tkinter), about half a minute; needs ffmpeg for the media tests.
demucs/Whisper are replaced by small stand-ins, so no models are downloaded.

### -eof-
