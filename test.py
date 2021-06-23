# Algorithm W - Damas hindley milner


from collections import namedtuple                  # for easy acess of parameters of functions among other

# Expressions for AST

ELit = namedtuple('ELit', 'val')                    # Constant literals (int, bool, string)
EVar = namedtuple('EVar', 'name')                   # Variables
EAbs = namedtuple('EAbs', ['arg', 'body'])          # (Lambda Abs) function [(Abs)traction] : \{arg} {body}
EApp = namedtuple('EApp', ['fun', 'arg'])           # Function [(App)lication] : f x
ELet = namedtuple('ELet', ['var', 'val', 'body'])   # [Let] Binding

# TYPES [Can also defined classes so as to print them from methods]

TLit = namedtuple('TLit', 'name')                 # Base types
TInt = TLit('TInt')                               # For integers (1, 2, ...)
TBool = TLit('TBool')                             # For Booleans (True, False)
TVar = namedtuple('TVar', 'name')                 # For Variables (x, y, z)
TFun = namedtuple('TFun', ['arg', 'result'])      # (TArg) -> (TReturn)

# For all {a, b} (bound_types) : {a->b->a} (type)
# TFun(TVar(a), TFun(TVar(b), TVar(a)))

TScheme = namedtuple('TScheme', ['bound_type', 'type'])


# Changes environment / variable according to [new?] substitutions

def substitute(substitution, type_var):

    """
    :param substitution: {a : int, b : (int->int), ...}
    :param type_var:
    :return changes and return the type_ variable according to [new ?] substitutions
    """
    
    if isinstance(type_var, TLit):
        return type_var
    if isinstance(type_var, TVar):
        if type_var in substitution:
            return substitute(substitution, substitution[type_var])
        else:
            return type_var
    if isinstance(type_var, TFun):
        return TFun(substitute(substitution, type_var.arg),
                    substitute(substitution, type_var.result))
    if isinstance(type_var, TScheme):
        type_only_subs = {x : y for x, y in substitution.items()
                        if x not in type_var.bound_type}
        return TScheme(type_var.bound_type, substitute(type_only_subs, type_var.type))
    if isinstance(type_var, dict):
        return {x : substitute(substitution, y)
                for x, y in type_var.items()}

# converts Type scheme to a type

def instantiate(t_scheme):
    """
    :param t_scheme: (for_all a, b: a->b)
    :return: (a->b) where 'a, b' are a fresh type like Int or Bool or TFunc
    """
    if isinstance(t_scheme, TScheme):
        new_sub = {type_: get_type_variable() for type_ in t_scheme.bound_type}
        return substitute(new_sub, t_scheme.type)
    return t_scheme


# UNIFICATION - makes new substitutions

def unification(a, b):
    """
    :param a: type_variable to bind to
    :param b: type
    :return: substitution : {a : int, b: int->int, a: b->b}
    """
    if isinstance(a, TLit) and isinstance(b, TLit):
        if a == b:
            return {}
        else :
            raise TypeError
    if isinstance(a, TVar):
        return {a : b}
    if isinstance(b, TVar):
        return {b : a}
    if isinstance(a, TFun) and isinstance(b, TFun):
        temp1 = unification(a.arg, b.arg)
        temp2 = unification(substitute(temp1, a.result), substitute(temp1, b.result))
        temp1.update(temp2) # Union set operation
        return temp1
    
    raise TypeError


# Allots fresh variable

index = 0

def get_type_variable():
    global index
    temp = TVar(index)
    index += 1
    return temp


# Makes new TScheme's

def generalize(env, type_var): 
    return TScheme(free_var(type_var), type_var)

# collects all free variables 

def free_var(type_):
    if isinstance(type_, TLit):
        return set()
    if isinstance(type_, TVar):
        return {type_}
    if isinstance(type_, TFun):
        return free_var(type_.result) | free_var(type_.arg) # All the free variables by taking OR
    if isinstance(type_, TScheme):
        return free_var(type_.type) - type_.bound_types
    if isinstance(type_, dict):
        result = set()
        for x in type_.values():
            result |= free_var(x)
        return result
    

def inference_engine(env, expr):
    # can add EIf
    # can add ELetrec
    if isinstance(expr, ELit):
        # No additional information and type is same as expression
        return {}, TInt if expr.val == 'TInt' else TBool
    if isinstance(expr, EVar):
        # Must already know it's type
        if expr in env:
            return {}, instantiate(env[expr]) # in case of for_all (a) a we should give a fresh type

    if isinstance(expr, EAbs):
        # (\arg body)
        targ = get_type_variable()                                                 # binder context
        new_env = dict(env)
        new_env[expr.arg] = targ                                                   # inserting into old context
        sbody, tbody = inference_engine(new_env, expr.body)                           # infer for body in new context
        return sbody, TFun(substitute(sbody, targ), tbody)
    if isinstance(expr, EApp):
        # fun (arg)
        sfun, tfun = inference_engine(env, expr.fun)                                  # Targ -> Tres
        sarg, targ = inference_engine(substitute(sfun, env), expr.arg)                # Targ
        tresult = get_type_variable()                                                 # tresult for function application
        sub = unification(substitute(sarg, tfun), TFun(targ, tresult))                # consistency check and merge information
        sfun.update(sarg)
        sfun.update(sub)
        return sfun, substitute(sub, tresult)                                         # result type of the function
    if isinstance(expr, ELet):                                      
        # let var = val in body
        tvar = get_type_variable()
        new_env = dict(env)
        new_env[expr.var] = tvar
        sval, tval = inference_engine(new_env, expr.val)                            # type for val under new substitution
        sub1 = unification(tval, substitute(sval, tvar))                            # type of val == var should be same
        sub2 = substitute(sub1, tval)
        sval.update(sub1)
        new_env = substitute(sval, env)
        var_scheme = generalize(new_env, sub2)
        new_env[expr.var] = var_scheme
        sbody, tbody = inference_engine(new_env, expr.body)
        sval.update(sbody)
        return sval, tbody

    raise TypeError 

def infer(expr):
    env = {} # current alloted elements or [context] {type_var : t_scheme , type_var : type}
    sub, type_ = inference_engine(env, expr)
    # type_ {a, b} : TFun(a, b)
    return sub, generalize(env, type_)


def get_expr(type_, names):

    if isinstance(type_, TLit):
        if type_.name == 'TInt':
            return "Int"
        return "Bool"
    if type_ == 'TInt':
        return 'Int'
    elif type_ == 'TBool':
        return 'Bool'
    if isinstance(type_, TVar):
        return names[type_.name]
    if isinstance(type_, TFun):
        ret = "("
        if isinstance(type_.arg, TVar):
            ret += get_expr(type_.arg, names)
            ret += ")"
        elif isinstance(type_.arg, TFun):
            ret += get_expr(type_.arg, names)
            ret += ")"
        else:
            for a in type_.arg:
                ret += get_expr(a, names)
                ret += ","
            ret = ret[:-1]
            ret += ")"
        ret += "-> ("
        if isinstance(type_.result, TVar):
            ret += get_expr(type_.result, names)
            ret += ")"
        elif isinstance(type_.result, TFun):
            ret += get_expr(type_.result, names)
            ret += ")"
        else:
            for a in type_.result:
                ret += get_expr(a, names)
                ret += ","
            ret = ret[:-1]
            ret += ")"
        return ret

    raise RuntimeError

names = {}

def convert_into_readable(s : TScheme):
    # assuming not more than 26 free variables 
    if(s.bound_type == set()):
        print(get_expr(s.type, {}))
        return
    
    string = ""
    string += "for_all ("
    global names
    names = {}
    curr_char = 'a'
    for type_ in s.bound_type:
        names[type_.name] = curr_char
        string += curr_char + ","
        curr_char = chr(ord(curr_char) + 1)
    string = string[:-1]
    string += ")"
    string += ": " + get_expr(s.type, names)
    print(string)

def test():
    example1 = infer(ELet(EVar("x"), ELit('TInt'), EVar("x"))) # AST
    convert_into_readable(example1[1])
    # let x = 5 in x -> int
    example2 = infer(EAbs(EVar('x'), ELit('TInt')))
    convert_into_readable(example2[1])
    # \x 5 -> 
    example3 = infer(EAbs(EVar('x'), EVar('x')))
    convert_into_readable(example3[1])
    # \f f : id
    # for_all a, a->a
    example4 = infer(ELet(EVar('id'), EAbs(EVar('x'), EVar('x')), EVar('id')))
    # print()
    # print(example4)
    # print()
    convert_into_readable(example4[1])
    # let id = \f f in id
    # [c:d->d], for_all a, a->a
    example5 = infer(EAbs(EVar('x'), EAbs(EVar('y'), EApp(EVar('x'), EVar('y')))))
    convert_into_readable(example5[1])
    # print(example5)
    # \x (\y x y)
    # x: (a->b), y: a : (a -> b) -> (a -> b)
    # [\ : (a->b)], for all a, b (a->b) -> (a->b)
    example6 = infer(EAbs(EVar('f'), EAbs(EVar("x"), EApp(EVar("f"), EApp(EVar("f"), EVar("x"))))))
    convert_into_readable(example6[1])

if __name__ == '__main__':
    test()