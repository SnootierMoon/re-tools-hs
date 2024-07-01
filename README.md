# re-tools-hs

The code is probably very inefficient and ugly, but it works.

Run `ghc re_tools.hs && ./re_tools | dot -T svg > o.svg && open o.svg`.

The regex syntax supports a-zA-Z for the alphabet, concatenation, and 
union via `|` as usual. The following repetition modifiers are supported
as well: `?`, `+`, `*`, `{N}` (exactly N), `{LO,HI}` (LO-HI), `{LO,}` (LO-),
`{,HI}` (0-HI).
