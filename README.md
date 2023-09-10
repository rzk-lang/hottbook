# HoTT Book formalisations in Rzk

This repository contains formalisations that follow [the HoTT Book](https://homotopytypetheory.org/book/).

## Building locally

As an optional first step, prepare a python virtual environment (`python -m venv venv`) and then activate it (using `.\venv\Scripts\activate` on Windows, or `source venv/bin/activate` on Linux and macOS).

Then, install the project's dependencies:

```sh
pip install -r requirements.txt
```

Now, you can build and serve the documentation locally by running

```sh
mkdocs serve
```

The (locally built) documentation should be available at http://127.0.0.1:8000
