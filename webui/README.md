# PyJanus web playground

A small browser playground for PyJanus: edit a Janus program, pick the dialect
(`--std`), direction and mode, supply `read`/`scanf` input, and run it — output and
errors come straight back.  It is the PyJanus counterpart of Jana-JanusInterp's web
UI.

The front-end (`playground.html`) and the example programs (`examples.json`) are
**shared** by two interchangeable backends:

| backend | how to run | needs |
|---------|-----------|-------|
| **Python** (stdlib only) | `python3 -m jana_py.web` | Python + Unix resource limits |
| **Apache / PHP** | drop `webui/` in the docroot | PHP + `python3` + `timeout` |

Both use `jana_py.web` for rendering, saving, and running programs. PHP calls
its gateway, so both deployments enforce the same validation and execution limits.
The package and its matching `webui/` assets must be deployed together.

## Option 1 — Python server (no dependencies)

```bash
python3 -m jana_py.web                 # http://127.0.0.1:8000
python3 -m jana_py.web --host 0.0.0.0 --port 9000
```

## Option 2 — Apache + PHP

Copy this `webui/` directory under your web root (or alias a vhost to it):

```apache
# e.g. in a vhost / .conf
Alias /pyjanus /srv/PyJanus/webui
<Directory /srv/PyJanus/webui>
    Require all granted
    LimitRequestBody 262144
    DirectoryIndex index.php
    SetEnv PYJANUS_ROOT /srv/PyJanus      # dir that contains jana_py/
    SetEnv PYJANUS_PYTHON /usr/bin/python3
</Directory>
```

Then open `http://your-host/pyjanus/`.  Requirements on the server:

- PHP with `proc_open` enabled (the default),
- `python3` on `PATH` (or set `PYJANUS_PYTHON`) with the `jana_py` package
  importable from `PYJANUS_ROOT` (the directory that contains `jana_py/`),
- the `timeout` command (coreutils) — caps the complete gateway request at
  15 seconds, followed by a forced kill after 2 seconds if needed;
- Unix `resource` limits (`RLIMIT_AS`, `RLIMIT_CPU`, `RLIMIT_FSIZE`) and `flock`.
  Web execution fails closed if limits are unavailable; the ordinary CLI is unaffected.

Defaults if the env vars are unset: `PYJANUS_ROOT` = the parent of `webui/`,
`PYJANUS_PYTHON` = `python3`.  Quick local check without Apache:

```bash
php -S 127.0.0.1:8080 -t webui          # then open http://127.0.0.1:8080/
```

## Files

| file | role |
|------|------|
| `playground.html` | shared front-end (placeholders `%%EXAMPLES%%`, `%%STDS%%`) |
| `examples.json`   | shared example programs + the dialect list |
| `index.php`       | PHP backend (GET = page, POST = run) |
| `../jana_py/web.py` | Python backend (`python -m jana_py.web`) |

To add an example or change the UI, edit `examples.json` / `playground.html`
once — both backends pick it up.

## Notes / security

- Submitted input is passed through **stdin**, never interpreted as CLI options.
  Dialects, modes, and numeric options are validated; `-m` is limited to 1–64
  and `-p` to at most 2147483647 (primality is checked by the CLI).
- Web `#include` resolution is restricted to the bundled `jana_py/lib/` tree,
  including nested includes and resolved symlinks. The normal CLI retains local
  file includes and `-I` search paths.
- Each execution has a **10-second wall/CPU limit**, **256 MiB address-space
  limit**, and **1 MiB limit per output stream**. At most **4 executions** run
  concurrently across processes sharing `PYJANUS_SAVES`.
- JSON requests are limited to **256 KiB**, source to **64 KiB**, and standard
  input to **16 KiB**. Python serves at most 8 connections with 5-second socket
  timeouts. For Apache, also configure `RequestReadTimeout` and
  `MaxRequestWorkers`: PHP runs only after the web server receives the request.
- Saved data is safely encoded when embedded in HTML, including old saved links.
  Storage is limited to **1000 saves / 64 MiB**; remove old `.json` files when
  full. Do not remove active `.lock` files, which coordinate concurrent requests.
- These controls are not an OS sandbox. Keep the service behind access control
  for trusted users, run under a dedicated unprivileged account, and keep the
  package/library directories read-only to that account.

## URL parameters & sharing

- **Pick a parser from the URL**: `…/pyjanus-playground/?std=jana2014_in_out`
  opens with that dialect pre-selected (`?parser=…` also works).
- **Standard input**: the *standard input* box takes one value per line (or
  whitespace-separated); it is fed to the program's `read`/`scanf`.
- **Save / share a program**: the **Share** button stores the whole state
  (source, dialect, mode, direction, input) on the server and copies a *short*
  link `…/pyjanus-playground/?p=<hash>` (a 10-char content hash); open it later to
  restore everything.  Saves go to `PYJANUS_SAVES` (default
  `<PYJANUS_ROOT>/playground-saves`). This directory also holds execution locks
  and must be writable by the service account, even when only running programs.
  Keep it outside the document root and private (for example, owned by that
  account with mode `0700`), not world-writable. Programs are de-duplicated by
  content hash.
