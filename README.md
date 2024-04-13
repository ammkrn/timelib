# Timelib

A date and time library for Lean 4, implementing the proleptic Gregorian calendar.



## Documentation

To generate timelib's documentation, first update in `dev` mode as [doc-gen4][docgen] is an optional
dependency.

```text
> lake -R -Kenv=dev update
```

Then actually generate the documentation with

```text
> lake -R -Kenv=dev build Timelib:docs
```

Almost done, the HTML is in `.lake/build/doc`, but accessing it *via* a browser requires an HTTP
server. For instance, using [python's `http.server`][python server]:

```text
> python3 -m http.server -d .lake/build/doc
```

[docgen]: https://github.com/leanprover/doc-gen4
[python server]: https://docs.python.org/3/library/http.server.html
