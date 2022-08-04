# 5. Budge-TP докажувач на теореми

Budge-TP (b'dzh) е докажувач на теореми кој овозможува изразување на формални системи. Формалните системи се важни затоа што лежат во сржта на математиката. Семантиката на Budge-TP се состои само од замена на променливи и проверка на еднаквост (споредба на симболи). Иако семантиката е едноставна, сепак е доволно моќна да претстави кој било формален систем, вклучително и пресметување, како што ќе биде покажано.

## 5.1. Синтакса и семантика

Во рамките на Budge-TP, формален систем е дефиниран со торката $F = (R, V, T)$ заедно со функциите $subst_{rule}^n$ и $subst_{thm}^n$ каде што $R_n \in R$ е множество на правила од $n$ аргументи, $V$ е множество на променливи, а $T$ е множество од теореми. Правилото $r = (r_1, \ldots, r_n) \in R_n$ е претставено како низа од стрингови; може да се толкува како функција $r_1 \to \ldots \to r_n$, каде што аргументот $n$ претставува заклучок, а останатите претставуваат хипотези.

Нека $S \subseteq V \times T$ означува множество на замени, а $X[t/v]$ го означува изразот $X$ во кој секоја појава на $v$ се заменува со $t$. Се дефинира следната функција која врши замена на хипотезите и заклучокот на правилото:
$$ subst_{rule}^n(r, S) = {
\begin{cases}
subst_{rule}^n(r_1[t/v], \ldots, r_n[t/v], S \setminus \{(v, t) \}), & r = (r_1, \ldots, r_n) \land (v, t) \in S \\
r & S = \emptyset
\end{cases}}
$$

Нека $h = (h_1, \ldots, h_{n-1})$ каде $\forall i, h_i \in T$. Функцијата $subst_{thm}^{n-1}(h, S)$ се дефинира на сличен начин.

За изведување нови теореми, $t = subst_{rule}^1((r_n), S) \in T$ (т.е. $t$ е теорема) ако и само ако:
$$subst_{rule}^{n-1}((r_1, \ldots, r_{n-1}), S) = subst_{thm}^{n-1}(h, S)$$

Термините и аксиомите се претставуваат како 1-арни правила; за $n = 1$ важи $subst_{rule}^0((), S) = () = subst_{thm}^0((), S)$, т.е. сите 1-арни правила веќе се теореми: $\forall r, r \in R_1 \to r \in T$.

Иако се искористи теоријата на множества за да се претстави семантиката, ќе биде воведена попогодна синтакса. Секоја команда во Budge-TP е од форма:

```
r<name> : <expr> [-> <expr> [-> ... -> <expr>]]
t<name> : <ruleN> [x=X;y=Y;...] [arg1] [arg2] [...] [argn]
```

Синтаксата \texttt{r<name>} одредува правило, а \texttt{t<name>} одредува теорема. Секоја низа знаци е прифатена освен \texttt{':'} и \texttt{' '} (бел простор) за \texttt{<name>} и \texttt{'->'} за \texttt{<expr>}. Средните загради претставуваат незадолжителни вредности. Малите букви во изразот на правилото се сметаат за променлива и ќе се користат за замена.

Во дадено правило, сите изрази освен последниот се сметаат за хипотеза (аргументи што треба да се принесат кога се користат во теорема), а последниот е заклучокот. За теоремите, правилото \texttt{<ruleN>} ќе се примени на соодветните аргументи. Замената со теореми (\texttt{x} со теорема \texttt{X}; \texttt{y} со теорема \texttt{Y}...) ќе се изврши и во хипотезите на правилото и во дадениот аргумент на теоремата и тие ќе бидат унифицирани. Ако унификацијата е успешна, последниот аргумент од правилото \texttt{argn} ќе биде резултантната теорема.

## 5.2. Пример имплементација во Python

Во овој дел ќе биде дадена имплементација за пресметка на теореми во Python, каде се користи податочна структура речник (dict `env`) која претставува околина на правила и теореми.

Најпрво се започнува со воведување на функција која парсира правила со форматот `rule : x -> y -> z` и ќе ги зачува податоците `x` и `y` како хипотези, а `z` како заклучок.

```python
def parse_rules(rules):
    parsed_rules = {}

    # Split rules into hypotheses and conclusion
    for name in rules:
        rule = list(map(str.strip, rules[name].split('->')))
        parsed_rules[name] = {'hypotheses': rule[:-1],
                              'conclusion': rule[-1]}

    return parsed_rules
```

По парсирање на правилата, следно треба да се испарсираат теоремите. Тоа се прави на тој начин што во секоја теорема од форматот `theorem1 : a=A;b=B;... rule1 x y z` најпрво се зачувува кое правило се искористува `rule1`, а потоа се зачувуваат и хипотезите (аргументите) кои се користат на тоа правило `x`, `y`, `z` и исто така се парсираат замените `a=A;b=B` користејќи ја дополнителната функција `parse_replacements`.

```python
def parse_theorems(theorems):
    parsed_theorems = {}

    # Process theorems, checking for valid syntax and process replacements on the way
    for name in theorems:
        arguments = list(filter(lambda x: x, theorems[name].split(' ')))

        if len(arguments) < 1:
            raise Exception("Invalid syntax for theorem '%s'" % name)

        rule = arguments[0]
        replacements = arguments[1] if len(arguments) > 1 else None
        hypotheses = arguments[2:] if len(arguments) > 2 else []

        parsed_theorems[name] = {'rule': rule, 'replacements': parse_replacements(
            name, replacements), 'hypotheses': hypotheses}

    return parsed_theorems
```

Следната функција ќе испарсира замени од форматот `a=A;b=B;...`:

```python
def parse_replacements(theorem_name, replacements):
    parsed_replacements = {}

    if replacements == None:
        return parsed_replacements

    replacements = replacements.split(';')

    # Parses "x=X,y=Y,..." into a dictionary for easier substitution, checking syntax on the way
    for expr in replacements:
        replacement = expr.split('=', 1)
        if len(replacement) < 2 or len(replacement[0]) != 1 or not replacement[0].islower():
            raise Exception(
                "Invalid syntax for replacement '%s' in '%s'" % (expr, theorem_name))
        parsed_replacements[replacement[0]] = replacement[1]

    return parsed_replacements
```

По парсирање, следува функција која ќе пресметува околина која се содржи од парсирани правила и теореми:

```python
def calculate_environment(code):
    env = {'rules': {}, 'theorems': {}}
    types = {'r': 'rules', 't': 'theorems'}

    code = filter(lambda x: x, code.split('\n'))
    code = filter(lambda x: x, map(
        lambda line: line.split('#')[0], code))  # strip comments

    # Process every line in the code, checking for valid syntax and storing the data for further parsing
    for line in code:
        parsed_line = list(
            filter(lambda x: x, map(str.strip, line.split(':', 1))))

        if len(parsed_line) != 2:
            raise Exception("Invalid syntax: '%s'" % line)

        [name, expr] = parsed_line

        if name[0] not in types:
            raise Exception("Invalid variable name: '%s'" % name)

        ty = types[name[0]]

        if name in env[ty]:
            raise Exception("Name redeclaration: '%s'" % name)

        env[ty][name] = expr

    env['rules'] = parse_rules(env['rules'])
    env['theorems'] = parse_theorems(env['theorems'])

    return env
```

Суштинската функција е `apply_rule` каде за дадена околина и теорема, функцијата ќе ги изврши потребните замени и проверки со обид да ја изведе дадената теорема:

```python
def apply_rule(env, theorem, theorem_name):
    replacements = theorem['replacements']
    th_hypotheses = theorem['hypotheses']
    rule = theorem['rule']

    if rule not in env['rules']:
        raise Exception("Invalid rule: '%s'" % rule)

    ru_hypotheses = env['rules'][rule]['hypotheses'].copy()
    ru_conclusion = env['rules'][rule]['conclusion']

    for k, v in replacements.items():
        if not v or v not in env['theorems']:
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (v, theorem_name))

        replacements[k] = env['theorems'][v]

        if not isinstance(replacements[k], str):
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (v, theorem_name))

    # Process theorem's hypotheses by substituting for other theorems
    for i, h in enumerate(th_hypotheses):
        if h not in env['theorems']:
            raise Exception("Invalid theorem: '%s' in '%s'" %
                            (h, theorem_name))
        hypothesis = env['theorems'][h]

        for k, v in replacements.items():
            hypothesis = hypothesis.replace(k, v)

        th_hypotheses[i] = hypothesis

    for k, v in replacements.items():
        # Process rule's hypotheses by substituting the replacements
        for i in range(0, len(ru_hypotheses)):
            ru_hypotheses[i] = ru_hypotheses[i].replace(k, v)

        # Process conclusion by substituting the replacements
        ru_conclusion = ru_conclusion.replace(k, v)

    if ru_hypotheses != th_hypotheses:
        raise Exception("Hypotheses mismatch for '%s': cannot unify\n\t%s\nand\n\t%s" % (
            theorem_name, str(ru_hypotheses), str(th_hypotheses)))

    return ru_conclusion
```

Главното извршување на функциите се врши на следниот начин, каде сите заедно се повикуваат:

```python
if len(sys.argv) != 2:
    exit('Usage: python %s <filename.arw>' % sys.argv[0])

if not exists(sys.argv[1]):
    exit("Filename '%s' not found." % sys.argv[1])

with open(sys.argv[1]) as f:
    code = f.read()

env = calculate_environment(code)

for theorem_name in env['theorems']:
    theorem = env['theorems'][theorem_name]
    env['theorems'][theorem_name] = apply_rule(env, theorem, theorem_name)

for name in env['theorems']:
    if name[-1] == '!':
        continue
    print('%s : %s' % (name, env['theorems'][name]))
```

## 5.3. Пример теореми

### 5.3.1. MIU систем (синтакса на теорија на множества)

Нека $R = \{ \{ \vdash\texttt{MI}, \texttt{I} \}, \{ (\vdash\texttt{Mx}, \vdash\texttt{Mxx}) \} \}$, $V = \{ \texttt{x} \}$. Изборот на $R_1$ дозволува да се одбере $S = \{ (\texttt{x}, \texttt{I}) \}$; бидејќи \texttt{I} е 1-арно правило, $\texttt{I} \in T$. Слично, $\vdash \texttt{MI} \in T$. За да се докаже $\vdash\texttt{MII} \in T$, се користи правилото од $R_2$ и бидејќи $(\texttt{x}, \texttt{I}) \in S$, се добива $subst_{rule}^1((\vdash\texttt{Mx}), S) = \vdash\texttt{MI} = subst_{thm}^1((\vdash\texttt{MI}), S)$. По оваа замена се извршува унификација, а бидејќи аргументите на правилото се еднакви на хипотезите на теоремата, следува дека $subst_{rule}^1((\vdash\texttt{Mxx}), S) = \vdash\texttt{MII} \in T$.

### 5.3.2. MIU систем (Budge-TP синтакса)

Со следните команди се дефинираат термини:

```
rTmM : M
rTmI : I
rTmU : U
tmM! : rTmM
tmI! : rTmI
tmU! : rTmU

rTmxy : xy
```

Со следните команди се дефинира аксиомата:

```
rMI : |- MI
thMI : rMI
```

Следно, се дефинираат правилата за инференција како што беа дефинирани во 2:

```
r1 : |- xI -> |- xIU
r2 : |- Mx -> |- Mxx
r3 : |- xIIIy -> |- xUy
```

Пример докази за некои теореми:

```
thMII : r2 x=tmI! thMI

tmII! : rTmxy x=tmI!;y=tmI!
thMIIII : r2 x=tmII! thMII

thMUI : r3 x=tmM!;y=tmI! thMIIII
```

Од горниот код ќе бидат изведени и испечатени следните теореми:

```
thMI : |- MI
thMII : |- MII
thMIIII : |- MIIII
thMUI : |- MUI
```

### 5.3.3. Булова логика (Budge-TP синтакса)

Со следните команди се дефинираат основните правила на системот:

```
rId : |-a=>a
rFst : |-a/\b=>a
rSnd : |-a/\b=>b
rInj1 : |-a=>a\/b
rInj2 : |-b=>a\/b
rPair : |-a=>b -> |-a=>c -> |-a=>b/\c
rCase : |-a=>b -> |-a=>c -> |-a\/b=>c
rComp : |-a=>b -> |-b=>c -> |-a=>c
```

Со следните команди се дефинираат термини:

```
rTOr : a\/b
rTAnd : a/\b
rTImp : a=>b

rTW : W
tW! : rTW
rTX : X
tX! : rTX
rTY : Y
tY! : rTY
rTZ : Z
tZ! : rTZ
```

Пример доказ: $\vdash W \land X \land Y \land Z \to W \lor Y$

```
tW|Y! : rTOr a=tW!;b=tY!
tW&X! : rTAnd a=tW!;b=tX!
tW&X&Y! : rTAnd a=tW&X!;b=tY!
tW&X&Y&Z! : rTAnd a=tW&X&Y!;b=tZ!

t1Step1! : rInj2 a=tW!;b=tY!
t1Step2! : rSnd a=tW&X!;b=tY!
t1Step3! : rComp a=tW&X&Y!;b=tY!;c=tW|Y! t1Step2! t1Step1!
t1Step4! : rFst a=tW&X&Y!;b=tZ!
t1 : rComp a=tW&X&Y&Z!;b=tW&X&Y!;c=tW|Y! t1Step4! t1Step3!
```

Пример доказ: $\vdash W \land X \to X \land W$

```
t2Step1! : rSnd a=tW!;b=tX!
t2Step2! : rFst a=tW!;b=tX!
t2 : rPair a=tW&X!;b=tX!;c=tW! t2Step1! t2Step2!
```

Пример доказ: $\vdash Y \lor W \to W \lor Y$

```
tY|W! : rTOr a=tY!;b=tW!
tY|Y|W! : rTOr a=tY!;b=tY|W!

t3Step1! : rInj1 a=tY!;b=tW!
t3Step2! : rInj2 a=tW!;b=tY!
t3Step3! : rCase a=tY!;b=tY|W!;c=tW|Y! t3Step1! t3Step2!
t3Step4! : rInj2 b=tY|W!;a=tY!
t3 : rComp a=tY|W!;b=tY|Y|W!;c=tW|Y! t3Step4! t3Step3!
```

### 5.3.4. Budge-PL јазик (Budge-TP синтакса)

Budge-PL користи теорија на броеви и прости броеви за складирање на податоци (регистри). Со следниот пример ќе биде претставен Budge-PL во Budge-TP со два регистри, како понизок систем кој не се потпира на теоријата на броеви, туку на следните основни правила:

```
# Listi i broevi
rMkList : (x y)
rTmNil : NIL
rTm0 : 0
rTmS : Sx
rTmP : P

# Poceten program
rInitState : p (a b)

# Komandi 1, -1, 2, -2
rNextState+1 : (S0 x) (a b) -> x (Sa b)
rNextState-1 : (P0 x) (Sa b) -> x (a b)
rNextState+2 : (SS0 x) (a b) -> x (a Sb)
rNextState-2 : (PP0 x) (a Sb) -> x (a b)

# Komandi za ciklus na vtoriot register
rLoop2Base : ((SS0 x) y) (a 0) -> y (a 0)
rLoop2Succ : ((SS0 x) y) (a Sb) -> APPEND x ((SS0 x) y) z -> z (a Sb)
```

Заедно со следните помошни правила за листи:

```
# Spojuvanje na listi
rAppendNil : APPEND NIL y y
rAppendRec : APPEND x y z -> APPEND (a x) y (a z)
```

На пример, за да се пресмета програмот $((2, -2, 1))$ каде првиот регистар има вредност 1, а вториот 2, се користат следните правила по ред: `rInitState`, `rLoop2Succ`, `rNextState-2`, `rNextState+1`, `rLoop2Succ`, `rNextState-2`, `rNextState+1`, `rLoop2Base`:

```
# Termini
t0! : rTm0
t-1! : rTmP x=t0!
t-2! : rTmP x=t-1!
t1! : rTmS x=t0!
t2! : rTmS x=t1!
t3! : rTmS x=t2!
tNil! : rTmNil

# Programot ((2,-2,1)) so dopolnitelni termini potrebni za dokazot
tEgList1! : rMkList x=t1!;y=tNil!
tEgList2! : rMkList x=t-2!;y=tEgList1!
tEgList3! : rMkList x=t2!;y=tEgList2!
tEgList : rMkList x=tEgList3!;y=tNil!
tEgList4! : rMkList x=t-2!;y=tNil!
tEgList5! : rMkList x=t1!;y=tEgList
tEgList6! : rMkList x=t-2!;y=tEgList5!

# Spojuvanje na listi potrebni za dokazot
tAp1! : rAppendNil y=tEgList
tAp2! : rAppendRec x=tNil!;y=tEgList;z=tEgList;a=t1! tAp1!
tAp : rAppendRec x=tEgList1!;y=tEgList;z=tEgList5!;a=t-2! tAp2!

t1Init : rInitState p=tEgList;a=t1!;b=t2!

t1Loop1 : rLoop2Succ x=tEgList2!;y=tNil!;a=t1!;b=t1!;z=tEgList6! t1Init tAp
t1DecR2 : rNextState-2 x=tEgList5!;a=t1!;b=t1! t1Loop1
t1IncR1 : rNextState+1 x=tEgList;a=t1!;b=t1! t1DecR2

t1Loop2 : rLoop2Succ x=tEgList2!;y=tNil!;a=t2!;b=t0!;z=tEgList6! t1IncR1 tAp
t1DecR2' : rNextState-2 x=tEgList5!;a=t2!;b=t0! t1Loop2
t1IncR1' : rNextState+1 x=tEgList;a=t2!;b=t0! t1DecR2'

t1 : rLoop2Base x=tEgList2!;y=tNil!;a=t3!;b=t0! t1IncR1'
```

Со дадениот код од 5.2, може да се изведат следните теореми:

```
tEgList : ((SS0 (PP0 (S0 NIL))) NIL)
tAp : APPEND (PP0 (S0 NIL)) ((SS0 (PP0 (S0 NIL))) NIL) (PP0 (S0 ((SS0 (PP0 (S0 NIL))) NIL)))
t1Init : ((SS0 (PP0 (S0 NIL))) NIL) (S0 SS0)
t1Loop1 : (PP0 (S0 ((SS0 (PP0 (S0 NIL))) NIL))) (S0 SS0)
t1DecR2 : (S0 ((SS0 (PP0 (S0 NIL))) NIL)) (S0 S0)
t1IncR1 : ((SS0 (PP0 (S0 NIL))) NIL) (SS0 S0)
t1Loop2 : (PP0 (S0 ((SS0 (PP0 (S0 NIL))) NIL))) (SS0 S0)
t1DecR2' : (S0 ((SS0 (PP0 (S0 NIL))) NIL)) (SS0 0)
t1IncR1' : ((SS0 (PP0 (S0 NIL))) NIL) (SSS0 0)
t1 : NIL (SSS0 0)
```

Теоремата `t1Init` го претставува почетниот програм `(2, (-2, 1))` со состојба `(1 2)`, а `t1` ја претставува последната пресметка на `t1Init`, односно состојбата `(3 0)` - збирот на двата регистри.
