sage-config
===========

My SAGEmath configuration, in which I introduce the object `S` and all of its superpowers.

This code is here for a single purpose: to help me solve simple technical problem faster. I'm trying to determine how much DWIM is too much, how much type-instability and ambiguity is too much? But rather than talking, let me demonstrate.

```python
# Split a string into pairs, merge the pairs, cast to int, and discard below 50
sage: S(+S, int, S>50, S.chunks("22637406234619207234", 2))
[63, 74, 72]
# Solve an expression for zero or an equation
sage: S(S.sv, [x^2 + 3*x, sqrt(x) == 9])
[[x == -3, x == 0], [x == 81]]
# Parallel expression substitution
sage: S(x^2 + y^4, [x^2 == 3, y^2 == 5])
28
# Function composition
sage: S(bin, str, S.upper)(90)
'0B1011010'
# Cast an expression into a function
sage: S[sqrt(x) + x^2](9)
84
# Convenient access to numpy, sympy, scipy, mpl, etc.
sage: S.norm(S.r_[1:10])
16.881943016134134

```

For the gory details, please consult [the wiki](https://github.com/PythonNut/sage-config/wiki).

Installation
============
```bash
cd ~/.sage
git init
git remote add origin http://github.com/PythonNut/sage-config
git fetch -a
git checkout -t origin/master
```
