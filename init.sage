import numpy as np
import scipy as sp

try:
    import pandas as pd
    pandas = pd
except: pass

try:
    import matplotlib as mpl
    from matplotlib import pyplot as plt
    matplotlib = mpl
    pyplot     = plt
except: pass

try:
    import numexpr
    import theano
except: pass

try:
    import sklearn
except: pass

import collections as coll

numpy       = np
scipy       = sp
matplotlib  = mpl
collections = coll
inf         = infinity

from functools import *
from copy      import deepcopy
from functools import partial as p
from itertools import *
from operator  import *

from string import ascii_lowercase
alpha = ascii_lowercase
import sympy, re
latex.engine("pdflatex")

scalars = [Integer,int,str,float,sage.rings.real_mpfr.RealLiteral,Rational]

y, z, a, b, c, i, k, t = var("y,z,a,b,c,i,k,t")
theta = var("theta")
F, f, h, g = function("F,f,h,g")
Y = function("Y", x)
assume(x,"real")
assume(y,"real")
assume(z,"real")
assume(i,"integer")
assume(k,"integer")

def parsolve(tx,ty):
    import itertools as it
    x, y = var("x,y")
    vx, vy = tx.variables()[0], ty.variables()[0]
    eq_tx = solve(x==tx,vx)
    eq_ty = solve(y==ty,vy)
    solutions = set()
    for ix, iy in it.product(eq_tx,eq_ty):
        solutions.add(tuple(solve(ix.rhs() == iy.rhs(),y)))
    solutions = [i[0] if len(i) == 1 else i for i in solutions]
    if len(solutions) == 1:
        return solutions[0]
    else:
        return solutions
            
def r(deg): return (deg/180*pi)
def d(rad): return (rad/pi*180)

def comp(*args):
    def temp(x):
        for func in args:
            x=func(x)
        return x
    return temp


def pp(x,q=True):
    try:
        print "\n"
        print x._maxima_()
        print "\n"
    except: print x
    if q: return x

def Sv(f,*var,**kwargs):
    if not isinstance(f,list):
        args,f,var=[f]+list(var),[],[]
        for i in args:
            if not i.is_symbol():
                f.append(i)
            else: var.append(i)
    vars=set()
    for i in range(len(f)):
        for v in f[i].variables():
            vars.add(v)
        if f[i].is_relational():
            f[i]=(f[i].lhs()-f[i].rhs())
        f[i]=f[i]._sympy_()
    if var == []: var=list(vars)
    #print f,var
    out=sympy.solve(f,*var,dict=True,**kwargs)
    for i in range(len(out)):
        try:
            if type(out[i]) == tuple:
                out[i] = list(out[i])
            out[i] = out[i]._sage_()
        except AttributeError:
            try:
                for k in range(len(out[i])):
                    out[i][k] = out[i][k]._sage_()
            except AttributeError:
                pass
            #except TypeError:
            #    pass
    return out

def inverse(f,x=None):
    try:
        if not x:
            x=f.variables()[-1]
        y = var('y')
        g = (f - y).roots(x, multiplicities=False)
        return [expr.subs(y=x) for expr in g]
    except RuntimeError as e:
        return []
    
class Magic(object):
    """
    This is the magic SAGE class. It contains lots of functionality
    Magic
     - SymPy
     - LaTeX
    """

    # Wrappers for SymPy functionality
    class SymPy(object):
        # convert expression to SymPy
        @classmethod
        def cv(self, x):
            return x._sympy_()

        # simplify expression with SymPy
        @classmethod
        def simp(self, x):
            if x.is_relational():
                return self.simp(x.lhs()) == self.simp(x.rhs())
            return sympy.simplify(self.cv(x))._sage_()

        # expression substitution with SymPy
        @classmethod
        def subs(self, x, fr, to):
            if x.is_relational():
                return self.subs(x.lhs(),x) == self.subs(x.rhs(),x)
            return self.cv(x).subs(self.cv(fr),self.cv(to))._sage_()

        # expand expression with SymPy
        @classmethod
        def exp(self, x, **kwargs):
            if x.is_relational():
                return self.exp(x.lhs(),**kwargs) == self.exp(x.rhs(),**kwargs)
            return self.cv(x).expand(**kwargs)._sage_()

        # factor expression with SymPy
        @classmethod
        def fac(self, x):
            if x.is_relational():
                return self.fac(x.lhs()) == self.fac(x.rhs())
            return sympy.factor(self.cv(x))._sage_()

        # pretty print using SymPy
        @classmethod
        def pp(self, x):
            return sympy.pprint(self.cv(x), use_unicode=True)

    # handles LaTeX conversion
    class LaTeX(object):
        """What will eventually become a flexible LaTeX transcription subsystem"""
        # parse fractions in string
        @classmethod
        def fracParse(self, x):
            match = re.search(r"(\\f|\f)rac\{(?P<n>.*?)\}\{(?P<d>.*?)\}",x)
            if match:
                n = self.fracParse(match.group("n")) # numerator
                d = self.fracParse(match.group("d")) # denominator
                return self.fracParse(x.replace(match.group(),"(%s)/(%s)"%(n,d)))
            return x

        @classmethod
        def latexParse(self,x):
            if "re" not in dir():
                import re

            x = self.fracParse(x)
            replacements = [
                ("*", ["\times", r"\times", "\cdot"]),
                ("cos", ["\cos"]),
                ("sin", ["\sin"]),
                ("tan", ["\tan", r"\tan"]),
                ("atan", ["\tan^{-1}", r"\tan^{-1}", "\atan", r"\atan"]),
                ("acos", [r"\cos^{-1}", "\acos", r"\acos"]),
                ("asin", [r"\sin^{-1}", "\asin", r"\asin"]),
                ("+", ["++", "--"]),
                ("-", ["+-", "-+"]),
                (", ", ["\n",r"\\"]),
                (")*(", [")("]),
                ("", ["\right", r"\right", "\left"]),
                ("pi", ["\pi", r"\pi"]),
            ]

            d = {w: repl for repl, words in replacements for w in words}

            for match in d:
                x = x.replace(match, d[match])

            x = self.fracParse(x)

            for r in [
                (r"\(\((?P<x>\w+)\)\)"      , "(%s)"), # handles ((x))
                (r"\((?P<x>\w+)\)\/"        , "%s/" ), # handles (x)/1
                (r"\/\((?P<x>\w+)\)"        , "/%s" ), # handles 1/(x)
                #(r"\S(?P<x>[\+\-\*\/])\S" , " %s ")    # handles +,-,*,/
            ]:
                while re.search(r[0],x):
                    search = re.search(r[0],x)
                    print "match"
                    x = x.replace(search.group(),r[1]%search.group("x"))

            # fix braces (will be smarter in the future)
            x = x + ")" * (x.count("(") - x.count(")"))
            x = x + "]" * (x.count("[") - x.count("]"))
            x = x + "}" * (x.count("{") - x.count("}"))
            return x

    class Function(object):
        def __init__(self, f):
            if f.__class__ == Expression:
                def temp(x):
                    return f(*{str(f.variables()[0]):x})
            self.f = f
            
        def __mul__(self, o):
            if o.__class__ == self.__class__:
                def temp(x):
                    return o.f(self.f(x))
                return self.__class__(temp)
                
            elif o.__class__ == Expression:
                return self * self.__class__(o)
                
            def temp(x):
                return o(self.f(x))
            return self.__class__(temp)

        def __div__(self, o):
            if o.__class__ != self.__class__:
                o = self.__class__(o)
                
            def temp(x):
                return self.f(o.f(x))
            return self.__class__(temp)

        def __add__(self, x): return map(self, x)

        def __sub__(self, x): return self.__call__(x)
            
        def __call__(self,*args,**kwargs):
            return self.f(*args,**kwargs)

    # homebrew math functions
    class Math(object):
        @classmethod
        def cis(self, theta):
            return cos(theta) + I * sin(theta)

        @classmethod
        def proj(self, a, b):
            return (b.dot(a)/S.norm(a)^2)*(a)

    # a homebrew matrix implementation
    class Mat(np.matrix):
        from sagenb.misc.sageinspect import sagenb_getdef as inspect
        #def __new__(self, *args, **kwargs):
        #    if len(args) > 1 and Integer(len(args)).is_square():
        #        super.__new__(self, [args], **kwargs)
        #    else:
        #        super.__new__(self, *args, **kwargs)

        def __init__(self, *args, **kwargs):
            if len(args) > 1 and Integer(len(args)).is_square():
                super.__init__([args], **kwargs)
                self.reshape([int(S.m.sqrt(len(args)))]*2)

        def S(self):
            return np.array(map(S,list(self))).reshape(self.shape)

        def getattr(self,attr):
            err = AttributeError("'Mat' object has no attribute '%s'"%attr)
            mods = [np.linalg,np,scipy]
            for mod in mods:
                if hasattr(mod, attr):
                    attr = getattr(mod,attr)
                    break
            else: raise err

            def f(x): return "=" not in x and "*" not in x
            sig = filter(f,inspect()[1:-1].split(","))
            if len(sig) == 1:
                def temp():
                    return attr(self)
                return Function(temp)
            elif len(sig) == 2:
                def temp(x):
                    return attr(self,x)
                return Function(temp)

            raise err

    def __init__(self):
        # shortcut tokens
        self.tokens = {
            # modifiers
            "r" : "rhs",
            "l" : "lhs",
            "+" : "sum",
            "N" : "N",
            "n" : "n",
            "|" : "abs",
            "f" : "factor",
            "I" : "imag",
            "R" : "real",
            "v" : "variables",
            "s" : "full_simplify",
            "a" : "assume",

            # identity
            "?r" : "is_real",
            "?=" : "is_relational",
            "?#" : "is_numeric",
            "?8" : "is_infinity",
            "?0" : "is_zero",
            "?1" : "is_one",
            "?x" : "is_symbol",
            "?+" : "is_positive",
            "?-" : "is_negative",
            "?." : "is_series",
            "?^" : "is_square",

            # conversion
            ">s"  : "_sympy_",
            ">S"  : "_sage_",
            ">sn" : "_singular_",
            ">o"  : "_octave_",
            ">l"  : "_latex_",
            ">k"  : "_kash_",
            ">p"  : "_pari_",
            ">m"  : "_maxima_",
            ">M" : "_mathematica>",
            ">mm" : "_mathml_",
            ">mp" : "_maple_",
        }

        # setup quick library access
        def _try_import(lst, module):
            try:
                lst.append(__import__(module))
            except: pass

        self.mro = [self.Math]
        
        _try_import(self.mro,"numpy")
        _try_import(self.mro,"numpy.linalg")
        _try_import(self.mro,"scipy")
        _try_import(self.mro,"matplotlib")
        _try_import(self.mro,"math")
        _try_import(self.mro,"cmath")
        _try_import(self.mro,"sympy")
        _try_import(self.mro,"pandas")
        _try_import(self.mro,"numexpr")
        _try_import(self.mro,"theano")
        _try_import(self.mro,"sklearn")
        _try_import(self.mro,"string")
        _try_import(self.mro,"functools")
        _try_import(self.mro,"itertools")
        _try_import(self.mro,"operator")
        _try_import(self.mro,"re")
        _try_import(self.mro,"sage.plot.colors")
        
        for unit_name in units.trait_names():
            self.mro.append(getattr(units,unit_name))

    def __str__(self):
        return "<SAGE magic stuff.>"
    __repr__ = __str__

    # parse arguments according to pattern
    @staticmethod
    def argParse(arg,*args):
        types = {
            "n" : [int,
                   float,
                   Rational,
                   Integer,
                   sage.rings.real_mpfr.RealLiteral],

            "f" : [float,
                   Rational,
                   sage.rings.real_mpfr.RealLiteral,
                   sage.rings.real_mpfr.RealNumber],

            "i" : [int, Integer],
            "s" : [coll.Iterable],
            "h" : [coll.Hashable],
            "e" : [Expression],
            "l" : [list, tuple],
            "s" : [str],
            "d" : [dict],
            "*" : [object],
            "a" : [np.ndarray],
        }
        arg = arg.split(",")

        parse = 0
        index = 0

        if arg == args == []:
            return True

        while parse < len(arg) or index < len(args):
            if index >= len(args) or parse >= len(arg):
                return False

            if arg[parse] in types:
                for t in types[arg[parse]]:
                    if isinstance(args[index],t):
                        parse += 1
                        index += 1
                        break
                else:
                    return False
                continue

            elif arg[parse][:-1] in types:
                if arg[parse][-1] == "*":
                    while True:
                        if index >= len(args):
                            break
                        for t in types[arg[parse][:-1]]:
                            if isinstance(args[index],t):
                                index += 1
                                break
                        else:
                            break
                    parse += 1

                elif arg[parse][-1] == "+":
                    if isinstance(args[index],coll.Iterable):
                        for item in args[index]:
                            for t in types[arg[parse][:-1]]:
                                if not isinstance(item,t):
                                    break
                            else: continue
                            break
                        else:
                            return True
                        parse += 1
                        index += 1
                    else:
                        return False
            elif arg[parse][:-2] in types:
                if arg[parse][-2:] == "++":
                    if isinstance(args[index],coll.Iterable):
                        for i in args[index]:
                            if not isinstance(i,coll.Iterable):
                                return False
                            for item in i:
                                for t in types[arg[parse][:-2]]:
                                    if not isinstance(item,t):
                                        break
                                else: continue
                                break
                            else: continue
                            break
                        else:
                            return True
                        parse += 1
                        index += 1
                    else:
                        return False
        return True

    # unravels single length lists
    @classmethod
    def unravel(self,x):
        if isinstance(x,coll.Iterable) and len(x) == 1:
            return self.unravel(x[0])
        else: return x

    @classmethod
    def enravel(self,x):
        if isinstance(x,coll.Iterable):
            return x
        else: return [x]

    def __process(self, x):
        remove = ["(",")"," "]
        out = str(x)
        for r in remove:
            out = out.replace(r,"")
        score = len(out)
        if str(x) == str(factor(x)):
            score = score * 0.7
        return score

    # get all possible alternate forms
    def forms(self,x, exp=True, fac=True, **kwargs):
        fast = True if "fast" not in kwargs else kwargs["fast"]

        try:
            forms = [x]
            simptype = [
                "simplify",
                "simplify_full",
                "simplify_rational",
                "simplify_exp",
                "simplify_log",
                "simplify_trig",
                "simplify_factorial",
                "simplify_radical"
            ]

            forms = list(forms)
            oldforms = [None]
            while list(set(oldforms)) != forms:
                oldforms = forms
                for i in forms[:len(forms)]:
                    if exp:
                        forms.append(expand(i))
                        if fast:
                            try:
                                forms.append(self.SymPy.exp(i,basic=True))
                                forms.append(self.SymPy.exp(i,basic=False))
                                forms.append(self.SymPy.exp(i,trig=True))
                            except: pass
                    if fac:
                        forms.append(factor(i))
                        if fast:
                            try: forms.append(self.SymPy.fac(i))
                            except: pass

                    try:
                        if len(i.variables()) == 1:
                           forms.append(i.partial_fraction(i.variables()[0]))
                    except: pass

                    try: forms.append(i.trig_reduce())
                    except: pass

                    try:
                        for s in simptype:
                            forms.append(getattr(x,s)())
                    except: pass

                    try:
                        forms.append(self.SymPy.simp(x))
                    except: pass

                forms = list(set(forms))

            forms = sorted(forms, key = self.__process)
            return forms
        except AttributeError:
            out = [x]

            # int
            try:
                if exp: out.append(factor(x))
                if fac: out.append(Rational(x))
                return out
            except TypeError:
                pass
                
            # float
            try:
                if fac: out.append(Rational(x))
                if fac: out.append(factor(Rational(x)))
                return out
            except TypeError:
                pass

            # Desperate. Any and all type castings.
            classes = [
                int,
                str,
                float,
                list,
                tuple,
                Matrix,
                factor,
                Rational,
                RealNumber,
                RealLiteral
            ]
            for cls in classes:
                try: out.append(cls(x))
                except: pass
            return out

    # get simplest form for Expression
    def ss(self, x):
        return self.forms(x)[0]

    def pp(self,x):
        return self.SymPy.pp(x)

    # substitute using SymPy or SAGE
    def sb(self, x, fr, to):
        try:
            # SymPy substitution is far more powerful
            # but does not support all edge cases.
            return self.SymPy.subs(x, fr, to)
        except AttributeError:
            return x.substitute(fr == to)

    def sub(self,exp,subs):
        x    = self.enravel(exp)
        subs = self.enravel(subs)
        out = []
        for i in x:
            if i.is_relational():
                temp = i
                for s in subs:
                    temp = self.sb(temp.lhs(),s.lhs(),s.rhs()) == \
                           self.sb(temp.rhs(),s.lhs(),s.rhs())
                out.append(temp)
            else:
                temp = i
                for s in subs:
                    temp = self.sb(temp,s.lhs(),s.rhs())
                out.append(temp)

        return self.unravel(out)

    def str(self, s, **kwargs):
        """What will become a flexible string interpretation system"""
        s = self.LaTeX.latexParse(s)
        replacements = [
            # base SI units
            ("S.meter", ["m", "meter", "meters"]),
            ("S.second", ["s", "second", "seconds"]),
            ("S.gram", ["g", "gram", "grams"]),
            ("S.kelvin", ["K", "kelvin"]),
            ("S.celsius",["C", "celsius"]),
            ("S.liter",["L", "liter", "liters"]),
            ("S.hertz",["Hz", "hertz"]),

            # prefix SI units (large)
            ("S.kilogram", ["kg", "Kg", "kilogram", "kilograms"]),
            ("S.kilometer", ["km", "Km", "kilometer", "kilometers"]),

            # prefix SI units (small)
            ("S.miligram", ["mg", "miligram", "miligrams"]),
            ("S.milimeter", ["mm", "milimeter", "milimeters"]),
            ("S.milisecond", ["ms", "milisecond", "miliseconds"]),

            # standard time units
            ("S.hour", ["hr", "hour", "hours"]),
            ("S.day", ["dy", "day", "days"]),
            ("S.week", ["wk", "week", "weeks"]),
            ("S.year", ["yr", "year", "years"]),

            # imperial units (length)
            ("S.foot", ["ft", "foot", "feet"]),
            ("S.yard", ["yd", "yard", "yards"]),
            ("S.inch", ["in", "inch", "inches"]),
            ("S.mile", ["mi", "mile", "miles"]),

            # imperial units (weight)
            ("S.pound", ["lb", "pound", "pounds"]),
            ("S.ton", ["ton", "tons"]),

            # imperial units (volume)
            ("S.cup", ["cup", "cups"]),
            ("S.teaspoons",["tsp", "teaspoon", "teaspoons"]),
            ("S.tablespoons",["tbsp", "tablespoon", "tablespoons"]),

            # angular units
            ("S.radian", ["radian", "radians", "rad"]),
            ("units.angles.degree", ["degree", "degrees", "deg"]),
            ("(S.radian*2*pi)", ["revolutions", "revolution", "rev"]),

            # units of force
            ("S.newton", ["newton", "newtons", "N"]),
            ("(S.newton*1e3)", ["kilonewton", "kilonewtons", "kN"]),
            ("(S.newton*1e6)", ["meganewtons", "meganewtons", "MN"]),
            
            # misc SI units
            ("S.joule", ["joule", "joules", "J"]),
            ("(S.joule*1e3)", ["kilojoule", "kilojoules", "kJ"]),
            ("(S.joule*1e6)", ["megajoule", "megajoules", "MJ"]),

            ("S.watt", ["watt", "watts", "W"]),
            ("(S.watt*1e3)", ["kilowatt", "kilowatts", "kW"]),
            ("(S.watt*1e6)", ["megawatt", "megawatts", "MW"]),

            ("S.volt", ["volt", "volts", "V"]),
            ("(S.volt*1e3)", ["kilovolt", "kilovolts", "kV"]),
            ("(S.volt*1e6)", ["megavolt", "megavolts", "MV"]),

            ("S.amp", ["amp", "amps", "A"]),
            ("(S.amp*1e3)", ["kiloamp", "kiloamps", "kA"]),
            ("(S.amp*1e6)", ["megaamp", "megaamps", "MA"]),

            # composite units
            ("(S.kilometer/S.hour)", ["kmh"]),
            ("(S.mile/S.hour)", ["mph"]),
            ("(S.hertz/60)", ["bpm"]),
            ("(S.radian*2*pi)/S.minute", ["rpm"]),
            ("S.horsepower", ["horsepower", "hp"]),

            # LaTeX oerators
            ("*", ["\mul", "\times", "\\times", "\cdot"]),
            ("/", ["\div"]),
        ]

        d = {w: repl for repl, words in replacements for w in words}
        def fn(match):
            return d[match.group()]

        s = re.sub('|'.join(r'\b{0}\b'.format(re.escape(k)) for k in d), fn, s)
        return sage_eval(s,locals=globals())

    def __getitem__(self,x):
        if self.argParse("i",x):
            def get_at(t):
                return t[int(x)]
                return self.Function(get_at)

        elif self.argParse("s",x):
            def get_mod(t):
                return getattr(t,self.tokens[x])()
            return self.Function(get_mod)

        elif self.argParse("*++",x):
            return matrix(x)

        elif self.argParse("n+",x):
            return vector(x)

        elif self.argParse("e+", x):
            return self.unravel(map(S.forms, x))

        elif self.argParse("l",x):
            def get_at(t):
                tmp = t
                for i in x:
                    tmp = tmp[i]
                    return tmp
            return self.Function(get_at)

        elif self.argParse("f",x):
            return np.array([cos(r(x)), sin(r(x))])

        elif self.argParse("e",x):
            def substitute(t):
                return self.sb(x,x.variables()[0],t)
            return self.Function(substitute)

    # resolve methods used in other libraries
    def __getattr__(self,x):
        for lib in self.mro:
            try:
                return getattr(lib,x)
            except AttributeError:
                pass
        raise AttributeError("'Magic' object has no attribute '%s'"%x)

    # the automagic function!
    def __call__(self,*args,**kwargs):
        if self.argParse("f",*args):
            return Rational(args[0])

        elif self.argParse("i",*args):
            return factor(args[0])

        elif self.argParse("s",*args):
            return self.str(args[0],**kwargs)

        elif self.argParse("a*",*args):
            return self.unravel(map(list,args))

        elif self.argParse("n*",*args):
            return np.array(args)

        elif self.argParse("e,n,n",*args):
            v, e = args[0].variables()[0], args[0]
            return S.sub(e,[v == args[2]]) - S.sub(e,[v == args[1]])

        elif self.argParse("e,n,n,e", *args):
            e, v = args[0], args[3]
            return S.sub(e,[v == args[2]]) - S.sub(e,[v == args[1]])

        elif self.argParse("e*",*args):
            return self.unravel(map(self.ss,args))

        elif self.argParse("e,e+",*args):
            sub = [(eq.lhs(),eq.rhs()) for eq in args[1]]
            temp = args[0]
            for i in sub:
                temp = self.sub(temp,[i[0]==i[1]])
            return temp

        elif self.argParse("e+,e+", *args):
            out = []
            for x in args[0]:
                out.append(self(x,args[1]))
            return out

        elif self.argParse("*++",*args):
            return self.array(self.unravel(args[0]))
            return self.Mat(self.enravel(self.unravel(args[0])))

        elif self.argParse("n+", *args):
            return vector(args[0])

        elif self.argParse("e+",*args):
            return self.unravel(map(self.ss,args[0]))

        elif len(args) == 1 and str(type(args[0])) == "<type 'function'>":
            return self.Function(args[0])

    # proxy functions for common stuff
    def __add__(self,x):
        if self.argParse("i",x):
            return xrange(x)
        elif self.argParse("l",x):
            return max(x)
        elif self.argParse("s",x):
            out = []
            for i in x.split(","):
                if self.re.match("^\w+$",i) and i not in dir():
                    out.append(var(i))
                elif self.re.match("^\w+\[.*\]$",i) and i[:i.index("[")] not in dir():
                    v=var(i[:i.index("[")])
                    mods = i[i.index("[")+1:i.index("]")]
                    modmap = {
                        "+" : var("x") > 0,
                        "-" : var("x") < 0,
                        "*" : var("x") != 0,
                        "z" : "integer",
                        "r" : "real",
                        "c" : "complex",
                        "q" : "rational"
                    }
                    for i in mods:
                        i=i.lower()
                        if modmap[i].__class__ == Expression:
                            modmap[i](x=v).assume()
                        else:
                            assume(v,modmap[i])
                    out.append(v)
                elif self.re.match("^\w+\{.*\}$",i) and i[:i.index("{")] not in dir():
                    v=var(i[:i.index("{")])
                    for i in i[i.index("{")+1:i.index("}")].split(","):
                        sage_eval(i,locals={str(v):v}).assume()
                    out.append(v)
                elif self.re.match("^\w+\(\)$",i) and i[:-2] not in dir():
                    out.append(function(i[:-2]))
                elif i in dir():
                    out.append(eval(i))
            return out

    def __sub__(self,x):
        if self.argParse("i",x):
            return xrange(1,x)
        elif self.argParse("l",x):
            return min(x)

    def __mul__(self,x):
        if self.argParse("i",x):
            return factor(x)
        elif self.argParse("f",x):
            return Rational(x)

    def __invert__(self):
        return Primes()

S = Magic()

%rehashx
