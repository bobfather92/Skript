# Skript end-to-end tests

These Playwright tests run Skript through the same browser UI used by the desktop app. The test server imports the real Python handler and writes only inside `tmp/e2e-data`; it never opens native dialogs or modifies the user's Documents folder.

## Install

```powershell
npm install
npm run e2e:install
```

On Windows the suite uses an installed Microsoft Edge or Google Chrome executable when available, so the browser-install command is optional. Set `$env:PW_EXECUTABLE_PATH` to select a different browser. With no system browser or override, Playwright uses its downloaded Chromium build.

Set `PYTHON` when Python is not available as `python`:

```powershell
$env:PYTHON = "C:\path\to\python.exe"
```

## Run

```powershell
npm run e2e
npm run e2e:headed
npm run e2e:debug
```

Open the latest HTML report with:

```powershell
npm run e2e:report
```

The run also writes JSON and JUnit reports to `test-results/`. Failed tests retain a screenshot, Playwright trace, and captured browser errors. Set `$env:PW_VIDEO = "1"` after installing Playwright's FFmpeg component to retain failure videos as well.

## Coverage

- Startup and dismissal of the welcome wizard.
- Screenplay editing and automatic element transitions.
- Compact touch-device layout.
- Desktop-service save followed by local-picker load.
- Opening an existing `.script` file.
- Fountain import and element classification.
- Word and Final Draft download integrity.
- Final Draft v5 and Fade In v2 real-file parsing, metadata preservation, dual-dialogue handling, and structural FDX round trips.
- PDF export invoking the local print path.
- JavaScript exceptions, console errors, and failed same-origin requests.

## Adding workflows

Use `support/skript-page.js` for shared user actions. Prefer visible controls and `data-testid` selectors, then assert the resulting UI or file output. Each test receives a fresh browser context, while the backend remains isolated and runs once for the suite.
