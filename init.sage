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
Y = function("Y")(x)
assume(x,"real")
assume(y,"real")
assume(z,"real")
assume(i,"integer")
assume(k,"integer")


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

class MetaLambdaBuilder(type):
    import operator

    def __init__(self, *args, **kw):
        super(MetaLambdaBuilder, self).__init__(*args, **kw)
        attr = '__{}__'

        for op in (x for x in dir(operator) if not x.startswith('__')):
            oper = getattr(operator, op)

            def func(self, n, oper=oper):
                def temp(x):
                    try:
                        return oper(self.func(x), n)
                    except AttributeError:
                        return oper(x, n)
                return LambdaBuilder(temp)

            def rfunc(self, n, oper=oper):
                def temp(x):
                    try:
                        return oper(n, self.func(x))
                    except AttributeError:
                        return oper(n, x)
                return LambdaBuilder(temp)

            setattr(self, attr.format(op), func)
            setattr(self, attr.format('r' + op), rfunc)

class LambdaBuilder():
    __metaclass__ = MetaLambdaBuilder
    def __init__(self, func):
        self.func = func

    def __call__(self, arg):
        out = self
        while True:
            try: out = out.func(arg)
            except: break
        return out

# Now play with the function f
class Magic(object):
    """
    This is the magic SAGE class. It contains lots of functionality
    Magic
     - SymPy
     - LaTeX
    """
    __metaclass__ = MetaLambdaBuilder

    class my_RealDistribution(RealDistribution):
        def __call__(self, x1, x2 = float("-inf")):
            try:
                a1 = self.cum_distribution_function(x1)
                a2 = self.cum_distribution_function(x2)
                return abs(a1 - a2)
            except: pass
            return numpy.linalg.norm(x1)

        def __getitem__(self, x1):
            return self.cum_distribution_function_inv(x1)

    norm = my_RealDistribution("gaussian", 1)

    def inverse(self, f, x=None):
        try:
            if not x:
                x=f.variables()[-1]
            y = var('y')
            g = (f - y).roots(x, multiplicities=False)
            return [expr.subs(y=x) for expr in g]
        except RuntimeError as e:
            return []

    def parsolve(self, tx,ty):
        import itertools as it
        x, y = var("x,y")
        vx, vy = tx.variables()[0], ty.variables()[0]
        eq_tx = solve(x==tx,vx)
        eq_ty = solve(y==ty,vy)
        solutions = set()
        for ix, iy in it.product(eq_tx,eq_ty):
            solutions.add(tuple(solve(ix.rhs() == iy.rhs(),y)))
            solutions =  map(self.unravel, solutions)
        return self.unravel(solutions)

    def sv(self,f,*var,**kwargs):
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
        # return out
        ret = []
        for solution in out:
            solution = [k._sage_() == v._sage_() for k,v in solution.items()]
            ret.append(self.unravel(solution))
        return ret

    def unique(self, lst):
        return list(coll.OrderedDict.fromkeys(lst))

    def chunks(self, lst, n):
        return zip(*[iter(lst)]*n)

    def multimap(self, fns, lst):
        dummy = lst[0]
        filter_p = []

        for f in fns:
            temp = f(dummy)
            if isinstance(temp, bool):
                filter_p.append(True)
            else:
                filter_p.append(False)
                dummy = temp

        res = lst
        for f, is_filter in zip(fns, filter_p):
            if is_filter:
                res = filter(f, res)
            else:
                res = map(f, res)

        return res

    def iqr(self, data):
        q3 = numpy.percentile(data, 75, interpolation='higher')
        q1 = numpy.percentile(data, 25, interpolation='lower')
        return q3 - q1

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
            if isinstance(f,Expression):
                def temp(x):
                    return f(**{str(f.variables()[0]):x})
                self.f = temp
            else:
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
        self.mro.append(numpy.linalg)
        _try_import(self.mro,"scipy")
        try:
            import scipy.stats
            self.mro.append(scipy.stats)
        except: pass
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
        _try_import(self.mro,"collections")
        _try_import(self.mro,"random")

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
            "c" : [coll.Callable],
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
                                    return False
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
                                        return False
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

        try:
            if str(x) == str(factor(x)):
                score = score * 0.7
        except NotImplementedError: pass

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
                "canonicalize_radical",
                "simplify_log",
                "simplify_trig",
                "simplify_factorial",
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
            ("S.hertz",["hz", "Hz", "hertz"]),

            # prefix SI units (large)
            ("S.kilogram", ["kg", "Kg", "kilogram", "kilograms"]),
            ("S.kilometer", ["km", "Km", "kilometer", "kilometers"]),

            # prefix SI units (small)
            ("S.gram/1e3", ["mg", "miligram", "miligrams"]),
            ("S.meter/1e3", ["mm", "milimeter", "milimeters"]),
            ("S.second/1e3", ["ms", "milisecond", "miliseconds"]),

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
            sub = [[eq.lhs() == eq.rhs()] for eq in args[1]]
            temp = args[0]
            for item in sub:
                temp = self.sub(temp, item)
            return temp

        elif self.argParse("e+,e+", *args):
            out = []
            for x in args[0]:
                out.append(self(x,args[1]))
            return out

        elif self.argParse("*++",*args):
            return self.array(self.unravel(args[0]))
            return Matrix(self.enravel(self.unravel(args[0])))

        elif self.argParse("n+", *args):
            return vector(args[0])

        elif self.argParse("e+", *args):
            # Detect: [var == expr, ...]
            variables = set()
            for item in args[0]:
                if item.is_relational():
                    if not item.lhs().is_symbol():
                        break
                    variables.add(item.lhs())
                else: break
            else:
                if len(variables) == 1:
                    return self.unravel(map(self.rhs, args[0]))

            return self.unravel(map(self.ss,args[0]))

        elif self.argParse("c*", *args):
            temp = self.Function(args[0])
            for fun in args[1:]:
                temp = temp * fun
            return temp

        elif self.argParse("c*,**", *args):
            fns = []
            lsts = []
            for item in args:
                if isinstance(item, coll.Callable):
                    if isinstance(item, Expression):
                        fns.append(self.Function(item))
                    else:
                        fns.append(item)
                else:
                    lsts.append(item)

            return self.unravel([self.multimap(fns, lst) for lst in lsts])

    def __pos__(self):
        def temp(obj):
            return reduce(operator.add,obj)
        return self.Function(temp)

    def __invert__(self):
        return Primes()

S = Magic()

%rehashx
%autocall 1
