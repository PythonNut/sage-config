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

        sage_funcs = filter(lambda x:"sage.functions" in str(type(eval(x))), globals().keys())
        sage_funcs.extend(['sqrt']) # I'm not sure what's special about sqrt.
        for f in sage_funcs:
            def funfact(f):
                def func(self, *a, **kw):
                    def temp(x):
                        oper=eval(f)
                        try:
                            return oper(self.func(x))
                        except AttributeError:
                            return oper(x)
                    return LambdaBuilder(temp)
                return func

            setattr(self, f, funfact(f))

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
            try:
                out = out.func(arg)
            except:
                break
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

    class StatDistribution(object):
        import inspect

        def __init__(self, dist, fallback = None):
            self.dist = dist
            self.fallback = fallback
            argspec = self.inspect.getargspec(self._parse_args)
            self.order = len(argspec.args) - len(argspec.defaults)

        def __getattr__(self, name):
            return getattr(self.dist, name)

        def __call__(self, *args):
            try:
                # Ensure that all args can be cast to a float
                # Otherwise, raise Exception and switch to fallback
                if len(args) == 1 and isinstance(args[0], RealSet):
                    area = 0
                    for item in args[0]:
                        area += self.__call__(item.lower(), item.upper())
                    return area

                args = map(float, args)

                if len(args) == self.order:
                    base, arg = args[:-1], args[-1]
                    return self.cdf(arg, *base)
                elif len(args) == self.order + 1:
                    base, arg1, arg2 = args[:-2], args[-2], args[-1]
                    a1 = self.cdf(arg1, *base)
                    a2 = self.cdf(arg2, *base)
                    return abs(a1 - a2)
                else:
                    msg = "Expected {} or {} args, got {}."
                    raise TypeError(msg.format(
                        self.order,
                        self.order + 1,
                        len(args)
                    ))
            except TypeError:
                if not self.fallback:
                    raise
                return self.fallback(*args)

        def __getitem__(self, x1):
            if not isinstance(x1, coll.Iterable):
                x1 = (x1,)

            if len(x1) == self.order:
                base, arg = x1[:-1], x1[-1]
                if arg > 1:
                    arglist = list(base)
                    arglist.append((1 - arg/100)/2)
                    return abs(self[arglist])
                return self.ppf(arg, *base)
            else:
                msg = "Expected {} args, got {}."
                raise TypeError(msg.format(self.order, len(x1)))

    class IterOperator(object):
        def __init__(self, func, *args, **kwargs):
            self.func, self.args, self.kwargs = func, args, kwargs
        def __call__(self, *args):
            return self.func(*list(args)+list(self.args), **self.kwargs)

    class IterSortOperator(IterOperator):
        def __call__(self, *args, **kwargs):
            if len(args) == 1 and isinstance(args[0], coll.Callable):
                return self.__class__.__bases__[0](sorted, key=args[0])
            elif isinstance(args[0], numpy.ndarray):
                return numpy.sort(*args, **kwargs)
            else:
                return super(self.__class__, self).__call__(*args)

    sort = IterSortOperator(sorted)
    reverse = IterOperator(lambda x: list(reversed(x)))

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

        # Automatically simplify resulting expression
        variables = set()
        for item in ret:
            if not item.lhs().is_symbol():
                break
            variables.add(item.lhs())
        else:
            if len(variables) == 1:
                return self.unravel(map(self.rhs, ret))

        return self.unravel(ret)

    def unique(self, lst):
        return list(coll.OrderedDict.fromkeys(lst))

    def chunks(self, lst, n):
        return zip(*[iter(lst)]*n)

    def multimap(self, fns, lst):
        res = lst
        for f in fns:
            if isinstance(f, self.IterOperator):
                res = f(res)
                continue
            try:
                temp = map(f, res)
                if all(isinstance(x, bool) for x in temp):
                    temp = filter(f, res)
            except TypeError:
                temp = f(res)
            res = temp

        return res

    def iqr(self, data):
        q3 = numpy.percentile(data, 75, interpolation='higher')
        q1 = numpy.percentile(data, 25, interpolation='lower')
        return q3 - q1

    def lhs(self, expr): return expr.lhs()
    def rhs(self, expr): return expr.rhs()

    def pm(self, base, delta = 0):
        if delta == 0: delta, base = base, 0
        return RealSet(base - delta, base + delta)

    # Wrappers for SymPy functionality
    class SymPy(object):
        # convert expression to SymPy
        @classmethod
        def cv(self, x):
            return x._sympy_()

        @classmethod
        def dispatch_relational(self, x, func, **kwargs):
            if x.is_relational():
                l = sageobj(func(self.cv(x.lhs()), **kwargs))
                r = sageobj(func(self.cv(x.rhs()), **kwargs))
                return l == r
            return sageobj(func(self.cv(x), **kwargs))

        @classmethod
        def simplify(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.simplify, **kwargs)

        @classmethod
        def subs(self, x, fr, to):
            if x.is_relational():
                return self.subs(x.lhs(),x) == self.subs(x.rhs(),x)
            return self.cv(x).subs(self.cv(fr),self.cv(to))._sage_()

        @classmethod
        def expand(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.expand, **kwargs)

        # factor expression with SymPy
        @classmethod
        def factor(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.factor, **kwargs)

        @classmethod
        def separatevars(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.separatevars, **kwargs)

        @classmethod
        def besselsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.besselsimp, **kwargs)

        @classmethod
        def logcombine(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.logcombine, **kwargs)

        @classmethod
        def expand_power_exp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.expand_power_exp, **kwargs)

        @classmethod
        def expand_power_base(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.expand_power_base, **kwargs)

        @classmethod
        def expand_log(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.expand_log, **kwargs)

        @classmethod
        def radsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.radsimp, **kwargs)

        @classmethod
        def collect_sqrt(self, x, **kwargs):
            from sympy.simplify.radsimp import collect_sqrt
            return self.dispatch_relational(x, collect_sqrt, **kwargs)

        @classmethod
        def collect_const(self, x, **kwargs):
            from sympy.simplify.radsimp import collect_const
            return self.dispatch_relational(x, collect_const, **kwargs)

        @classmethod
        def ratsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.ratsimp, **kwargs)

        @classmethod
        def trigsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.trigsimp, **kwargs)

        @classmethod
        def powsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.powsimp, **kwargs)

        @classmethod
        def powdenest(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.powdenest, **kwargs)

        @classmethod
        def combsimp(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.combsimp, **kwargs)

        @classmethod
        def sqrtdenest(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.sqrtdenest, **kwargs)

        @classmethod
        def hyperexpand(self, x, **kwargs):
            return self.dispatch_relational(x, sympy.hyperexpand, **kwargs)

        # pretty print using SymPy
        @classmethod
        def pp(self, x):
            return sympy.pprint(self.cv(x), use_unicode=True)

        # numeric simplification
        @classmethod
        def nsimp(self, x):
            return sageobj(sympy.nsimplify(self.cv(x)))

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
        # scipy.stats
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

        import scipy.stats
        stat_dists = []
        stat_dists += scipy.stats._continuous_distns.__dict__.values()
        stat_dists += scipy.stats._discrete_distns.__dict__.values()
        for name, obj in scipy.stats.__dict__.items():
            if not hasattr(obj, "cdf"): continue
            if not hasattr(obj, "_parse_args"): continue
            if obj in stat_dists:
                old_attr = None
                try:
                    old_attr = getattr(self, name)
                except AttributeError:
                    pass
                dist_wrapper = self.StatDistribution(obj, old_attr)
                self.__dict__[name] = dist_wrapper

        self.mro.insert(2, scipy.stats)

        for unit_type in units.__dict__["_Units__data"].keys():
            attr = getattr(units, unit_type)
            if isinstance(attr, sage.symbolic.units.Units):
                self.mro.append(attr)

    def __str__(self):
        return "<SAGE magic stuff.>"
    __repr__ = __str__

    # parse arguments according to pattern
    @staticmethod
    def argParse(arg,*args):
        import inspect
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

            "m" : [sage.matrix.matrix.is_Matrix],
            "v" : [sage.structure.element.Vector],
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

        def is_thing(it, thing):
            if inspect.isclass(thing):
                return isinstance(it, thing)
            return thing(it)

        while parse < len(arg) or index < len(args):
            if index >= len(args) or parse >= len(arg):
                return False

            if arg[parse] in types:
                for t in types[arg[parse]]:
                    if is_thing(args[index],t):
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
                            if is_thing(args[index],t):
                                index += 1
                                break
                        else:
                            break
                    parse += 1

                elif arg[parse][-1] == "+":
                    if isinstance(args[index],coll.Iterable):
                        for item in args[index]:
                            for t in types[arg[parse][:-1]]:
                                if not is_thing(item,t):
                                    return False
                        parse += 1
                        index += 1
                    else:
                        return False
            elif arg[parse][:-2] in types:
                if arg[parse][-2:] == "++":
                    if isinstance(args[index],coll.Iterable):
                        for i in args[index]:
                            if not is_thing(i,coll.Iterable):
                                return False
                            for item in i:
                                for t in types[arg[parse][:-2]]:
                                    if not is_thing(item,t):
                                        return False
                        parse += 1
                        index += 1
                    else:
                        return False
        return True

    # unravels single length lists
    @classmethod
    def unravel(self,x):
        try:
            if isinstance(x,coll.Iterable) and len(x) == 1:
                return self.unravel(x[0])
        except: pass
        return x

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
            try:
                if str(x) == str(factor(x)):
                    score = score * 0.7
            except TypeError:
                pass
        except NotImplementedError: pass

        return score

    # get all possible alternate forms
    def forms(self, x, **kwargs):
        import copy
        import itertools
        import sys
        import sympy
        try:
            if x.is_relational():
                res = []
                op = x.operator()
                lhs = self.forms(x.lhs(), **kwargs)
                rhs = self.forms(x.rhs(), **kwargs)
                for l, r in itertools.product(lhs, rhs):
                    res.append(op(l, r))
                return res
        except AttributeError:
            pass

        fast = True if "fast" not in kwargs else kwargs["fast"]
        return_paths = False if "path" not in kwargs else kwargs["path"]
        limit = (10 if fast else 20) if "limit" not in kwargs else kwargs["limit"]
        progress = False if "progress" not in kwargs else kwargs["progress"]
        ratio = 2.5 if "ratio" not in kwargs else kwargs["ratio"]
        safe = True if "safe" not in kwargs else kwargs["safe"]

        def complexity_score(expr):
            weights = {
                "POW" : 1.5,
                "SIN" : 2,
                "COS" : 2,
                "TAN" : 2.5,
            }

            complexity = sympy.count_ops(expr, visual=True)
            for name, weight in weights.items():
                complexity = complexity.subs(sympy.Symbol(name), weight)
            complexity = complexity.replace(sympy.Symbol, type(sympy.S.One))

            return complexity

        simplifiers = {
            'simp'      : lambda x: [x.simplify()],
            'factorial' : lambda x: [x.simplify_factorial()],
            'full'      : lambda x: [x.simplify_full()],
            'hypergeom' : lambda x: [x.simplify_hypergeometric()],
            'rational'  : lambda x: [x.simplify_rational()],
            'rectform'  : lambda x: [x.simplify_rectform(complexity_measure=None)],
            'trig'      : lambda x: [x.simplify_trig()],
            'trig_red'  : lambda x: [x.trig_reduce()],
            'expand'    : lambda x: [x.expand()],
            'exp_sum'   : lambda x: [x.expand_sum()],
            'exp_trig1' : lambda x: [x.simplify_trig(expand=True)],
            'exp_trig2' : lambda x: [x.expand_trig()],
            'exp_trig3' : lambda x: [x.expand_trig(half_angles=True)],
            'exp_rat'   : lambda x: [x.expand_rational()],
            'factor'    : lambda x: [x.factor()],
        }

        if not safe:
            simplifiers.update({
                'radical'   : lambda x: [x.canonicalize_radical()],
                'real'      : lambda x: [x.simplify_real()],
                'log'       : lambda x: [x.simplify_log()],
                'exp_log1'  : lambda x: [x.expand_log()],
                'exp_log2'  : lambda x: [x.expand_log(algorithm='powers')],
            })

        def sympy_contains_decimal(x):
            if x.args:
                return any(map(sympy_contains_decimal,x.args))
            return x.is_real and not x.is_rational

        sympy_simplifiers = {
            'separate'   : 'separatevars',
            'bessel'     : 'besselsimp',
            'exp_log'    : 'expand_log',
            'log'        : 'logcombine',
            'rad'        : 'radsimp',
            'coll_sqrt'  : 'collect_sqrt',
            'coll_const' : 'collect_const',
            'rat'        : 'ratsimp',
            'trig'       : 'trigsimp',
            'pow'        : 'powsimp',
            'powdenest'  : 'powdenest',
            'pow_exp'    : 'expand_power_exp',
            'pow_base'   : 'expand_power_base',
            'comb'       : 'combsimp',
            'sqrtdenest' : 'sqrtdenest',
            'exp_hyper'  : 'hyperexpand'
        }

        def try_sympy_factory(sympy_name, **kwargs):
            def try_sympy(x):
                result = getattr(self.SymPy, sympy_name)(x, **kwargs)
                if (not sympy_contains_decimal(x._sympy_()) and
                    sympy_contains_decimal(result._sympy_())):
                    return []
                return [result]

            return try_sympy

        for name, simplifier in sympy_simplifiers.items():
            simplifiers['py_%s'%name] = try_sympy_factory(simplifier)

        # broken on current SymPy (fixed on master)
        # simplifiers['py_groebner'] = try_sympy_factory('trigsimp', method="groebner")
        simplifiers['py_trig_fu'] = try_sympy_factory('trigsimp', method="fu")

        if not safe:
            for name in ['pow', 'powdenest', 'pow_base', 'exp_log', 'log']:
                simplifier = sympy_simplifiers[name]
                simplifiers['py_%s_f'%name] = try_sympy_factory(simplifier, force=True)
        
        def try_partial_fractions(x):
            if len(x.variables()) == 1:
                return [x.partial_fraction(x.variables()[0])]
            return []

        def try_maxima_exponentialize(x):
            return [sageobj(x._maxima_().exponentialize())]

        def try_maxima_demoivre(x):
            return [sageobj(x._maxima_().demoivre())]

        simplifiers['part_frac'] = try_partial_fractions
        simplifiers['mx_euler'] = try_maxima_exponentialize
        simplifiers['mx_demoivre'] = try_maxima_demoivre

        forms = {x : []}
        old_forms = {}

        longest_output = -1
        form_count = 1
        original_score = complexity_score(x)

        while True:
            new_forms = {}
            for form, path in forms.items():
                for name, simplifier in simplifiers.items():
                    if progress:
                        message = '%d %s → %s'%(form_count, ' → '.join(path), name)
                        print message.ljust(longest_output) + "\r",
                        longest_output = max(longest_output, len(message))
                        sys.stdout.flush()

                    try:
                        for new_form in simplifier(form):
                            if "." in str(new_form) and '.' not in str(form):
                                print(form,path,name)
                            if not (new_form in forms or
                                    new_form in old_forms or
                                    new_form in new_forms):
                                new_score = complexity_score(new_form)
                                if new_score <= original_score * ratio:
                                    new_forms[new_form] = path + [name]
                                    form_count += 1
                    except (AttributeError, TypeError) as e:
                        pass

            forms.update(new_forms)
            old_forms.update(forms)
            forms = new_forms

            if len(old_forms) > limit:
                break

            if not new_forms: break

        if progress: print " " * longest_output + "\r",

        forms = list(old_forms.items())
        forms = sorted(forms,key=lambda x: complexity_score(x[0]))
        if not return_paths:
            forms = map(lambda x: x[0], forms)
        return forms

    # get simplest form for Expression
    def ss(self, x, **kwargs):
        return self.forms(x, **kwargs)[0]

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

    def source(self, name):
        for lib in self.mro:
            try:
                if isinstance(name, str):
                    getattr(lib, name)
                else:
                    if name not in lib.__dict__.values():
                        raise AttributeError()
                return lib
            except AttributeError:
                pass
        raise AttributeError("'Magic' object has no attribute '%s'"%name)

    # the automagic function!
    def __call__(self,*args,**kwargs):
        if self.argParse("f",*args):
            return S.ss(args[0], **kwargs)

        elif self.argParse("i",*args):
            return S.ss(args[0], **kwargs)

        elif self.argParse("s",*args):
            return self.str(args[0],**kwargs)

        elif self.argParse("a*",*args):
            return self.unravel(map(list,args))

        elif self.argParse("n*",*args):
            return vector(args)

        elif self.argParse("e,n,n",*args):
            v, e = args[0].variables()[0], args[0]
            return S.sub(e,[v == args[2]]) - S.sub(e,[v == args[1]])

        elif self.argParse("e,n,n,e", *args):
            e, v = args[0], args[3]
            return S.sub(e,[v == args[2]]) - S.sub(e,[v == args[1]])

        elif self.argParse("e*",*args):
            return self.unravel(map(lambda x: S.ss(x, **kwargs), args))

        elif self.argParse("e,e+",*args):
            sub = [[eq.lhs() == eq.rhs()] for eq in args[1]]
            temp = args[0]
            for item in sub:
                temp = self.sub(temp, item)
            return temp

        elif self.argParse("m*", *args) or self.argParse("v*", *args):
            return self.unravel([m.apply_map(lambda x: S.ss(x, **kwargs))
                                 for m in args])

        elif self.argParse("e+,e+", *args):
            out = []
            for x in args[0]:
                out.append(self(x,args[1]))
            return out

        elif self.argParse("*++",*args):
            return matrix(self.enravel(self.unravel(args[0])))

        elif self.argParse("n+", *args):
            return vector(args[0])

        elif self.argParse("e+", *args):
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
%colors Linux
