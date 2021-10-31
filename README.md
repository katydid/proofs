# proofs
Proofs written in Coq for the core katydid validation algorithm

![Check Proofs](https://github.com/katydid/proofs/workflows/Check%20Proofs/badge.svg)

## Development

### Contributing

Please read the [contributing guidelines](https://github.com/awalterschulze/regex-reexamined-coq/blob/master/CONTRIBUTING.md).  They are short and shouldn't be surprising.

### Setup

1. Install [Coq 8.13.1](https://github.com/coq/coq/releases/tag/V8.13.1)
2. Remember to set coq in your PATH. For example, in your `~/.bash_profile` add `PATH="/Applications/CoqIDE_8.13.1.app/Contents/Resources/bin/:${PATH}"` and run `$ source ~/.bash_profile`.
3. Open CoqIDE by right clicking (since it is not properly signed for mac).
4. Run make in this folder.

### Clean

 - `make cleanall` cleans all files even `.aux` files.

### Regenerate Makefile

Coq version upgrade requires regenerating the Makefile with the following command:

```
$ coq_makefile -f _CoqProject -o Makefile
```

### VS Code

1. Install VS Code
2. Install the VSCoq extension
3. Go to settings and set your `CoqTop: Bin Path` to `/Applications/CoqIDE_8.13.1.app/Contents/Resources/bin`
4. Use Cmd+Option+Down and Cmd+Option+Left to walk through the proof

### Pair Programming

We have pair programming session on some Saturdays 14:00 - 17:00 UK time.
Please email [Walter](https://github.com/awalterschulze) if you would like to join us.
It would be helpful to understand how to use Coq's Inductive Predicates, but more advanced knowledge is not required.
