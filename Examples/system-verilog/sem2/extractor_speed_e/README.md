# Extractor speed receipt

The scratch-safe command

```text
TMPDIR=/scratch/thomas-ahle/gate/ls-sv3/tmp python3 tools/sv_extractor_speed.py
```

measured the parser-shaped package and generate hierarchy at 0.397s, 0.411s,
and 0.398s on three current-master runs. The source is generated in the
temporary directory by the tool, so no scratch path or generated envelope is
checked in.
