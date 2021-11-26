Proof of concept code from [AHHPVW].

[AHHPVW] Martin R. Albrecht, Christian Hanser, Andrea Hoeller, Thomas Pöppelmann, Fernando Virdia, Andreas Wallner, "Learning with Errors on RSA Co-Processors", 2018, https://eprint.iacr.org/2018/425

## Sagemath 9 instructions
To test the implementation in Sagemath 9, pytest needs to be installed.
```bash
$ sage -sh
(sage-sh) $ pip install pytest
(sage-sh) $ exit
```

Tests can then be run using
```bash
$ sage -t test.py
```
