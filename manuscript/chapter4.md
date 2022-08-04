# 4. Budge-PL програмски јазик

Budge-PL (b'dzh) е едноставен програмски јазик кој користи Геделово нумерирање за да ги претстави регистрите и нивните вредности користејќи ја фундаменталната теорема на аритметиката. На пример, за да се претстават вредностите $1$, $2$ и $3$ во меморија, се пресметува $2^1 \cdot 3^2 \cdot 5^3$ (првите три прости броеви 2, 3, 5 на степен на бројот на вредноста во соодветниот регистар), пристигнувајќи во состојбата $i = 2250$. Може да се екстрахираат $1$, $2$ и $3$ од $2250$ со користење на факторизација.

Budge-PL користи слични конструкции како FRACTRAN. Сепак, Budge-PL обезбедува попогоден начин за конструирање циклуси и користи цели броеви наместо дропки за означување на инструкции. Негативен цел број ќе ја намали вредноста на регистарот, додека позитивен цел број ќе ја зголеми вредноста на регистарот. Дополнително, програмскиот јазик обезбедува лесен начин за кодирање на циклуси со користење на вгнездени загради. Конечно, ги апстрахира простите броеви во кодот од програмерот.

![Budge-PL во Esolangs](images/budge-esolangs.png){ width=650px }

## 4.1. Синтакса и семантика

Податоците се претставени како $i \in \mathbb{N^+}$ (производ на прости броеви), а синтаксата на кодот претставена преку Backus-Naur формата е:

```
<posn>  ::= "1" | "2" | ...               <negn> ::= "-1" | "-2" | ...
<stmt>  ::= <posn> | <negn> | "("<posn>","<stmts>")"
<stmts> ::= <stmt>","<stmts> | <stmt>     <code> ::= "("<stmts>")"
```

Нека $p(n)$ е $n$-тиот прост број. Нека $sign(n) = 1$ ако $n>0$ и $-1$ во спротивно; ова ќе одреди дали треба да се множи или дели. Понатаму, со изразот $\forall x, n_x \in \mathbb{Z} \land n'_x \in \mathbb{Z}$, нека функцијата $E(i, s)$ ја претставува пресметката на низата $s$ (`<code>` ) за влез $i$, дефинирана на следниот начин:

$$ E(i, s) = {
\begin{cases}
E(i \cdot p(|n_0|)^{sign(n_0)}, (n_1, \ldots, n_k)) & s = (n_0, n_1, \ldots, n_k) \land i \cdot p(|n_0|)^{sign(n_0)} \in \mathbb{N}, \\
E(i, (n_1, \ldots, n_k)) & s = (n_0, n_1, \ldots, n_k) \land i \cdot p(|n_0|)^{sign(n_0)} \notin \mathbb{N}, \\
E(E(i, (n'_0, \ldots, n'_k)), s) & s = ((P, n'_0, \ldots, n'_k), n_0, \ldots, n_j) \land i \cdot p(|P|)^{-1} \in \mathbb{N}, \\
E(i, (n_0, \ldots, n_j)) & s = ((P, n'_0, \ldots, n'_k), n_0, \ldots, n_j) \land i \cdot p(|P|)^{-1} \notin \mathbb{N}, \\
i & {s = ()}\end{cases}} $$

Семантички, првиот случај се справува со зголемување/намалување на вредност во регистарот $n_0$. Вториот случај е за прескокнување на инструкција. Третиот и четвртиот случај го претставуваат почетокот и крајот на циклус (вгнездени загради).

## 4.2. Пример имплементација во Python

Во овој дел ќе биде дадена имплементација во Python, каде се користат листи од Python за да се претстави кодот од синтаксата дефинирана во 4.1:

\begin{minipage}{0.45\textwidth}
\begin{lstlisting}[language=Python]
def sign(x):
  return 1 if x >= 1 else -1
def p(x):
  (n, c) = (1, 0)
  while c < x:
    n += 1
    for i in range(2, n+1):
      if n % i == 0:
        break
    if i == n:
      c += 1
  return n
\end{lstlisting}
\end{minipage}
\hspace{0.5cm}
\begin{minipage}{0.45\textwidth}
\begin{lstlisting}[language=Python]
def evaluate(i, code):
  for el in code:
    if isinstance(el, list):
      while i % p(abs(el[0])) == 0:
        i = evaluate(i, el[1:])
    elif sign(el) == 1:
      i *= p(el)
    else:
      new_i = p(abs(el))
      if i % new_i == 0:
        i = int(i // new_i)
  return i
\end{lstlisting}
\end{minipage}

Заедно со следните помошни методи кои овозможуваат вредностите да бидат попогодно претставени како регистри, наместо како прости броеви:

\begin{minipage}[t]{0.45\textwidth}
\begin{lstlisting}[language=Python]
def get_registers(i):
  (r, reg) = ({}, 1)
  while i != 1:
    while i % p(reg) == 0:
      if reg not in r: r[reg] = 0
      r[reg] += 1
      i //= p(reg)
    reg += 1
  return r
\end{lstlisting}
\end{minipage}
\hspace{0.5cm}
\begin{minipage}[t]{0.45\textwidth}
\begin{lstlisting}[language=Python]
def set_registers(r):
  i = 1
  for reg in r:
    i *= p(reg) ** r[reg]
  return i
\end{lstlisting}
\end{minipage}

## 4.3. Пример програми

### 4.3.1. Збир на броеви (опис на пресметување)

За да се пресмета $E(2^3 \cdot 3^3, ((2, -2, 1)))$ се итерира низ низата $(-2, 1)$ се додека $\frac{i}{p(2) }$ повеќе не е цел број, односно $\frac{i}{3}$:

- Првично, $i = 2^3 \cdot 3^3 = 216$, а бидејќи $\frac{216}{3} = 72 \in \mathbb{N}$, пресметувањето продолжува.
- $p(|n|)^{sign(n)}$ за $n = -2$: $i' = p(2)^{-1} = 3^{-1}$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 216 \cdot i' = 72$.
- $p(|n|)^{sign(n)}$ за $n = 1$: $i' = p(1)^{1} = 2$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 72 \cdot i' = 144$.
- Во овој момент, се враќа назад и се проверува дали $\frac{144}{3} \in \mathbb{N}$ - пресметувањето продолжува.
- Се пресметува $p(|n|)^{sign(n)}$ за $n = -2$: $i' = p(2)^{-1} = 3^{-1}$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 144 \cdot i' = 48$.
- $p(|n|)^{sign(n)}$ за $n = 1$: $i' = p(1)^{1} = 2$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 48 \cdot i' = 96$.
- Во овој момент, се враќа назад и се проверува дали $\frac{96}{3} \in \mathbb{N}$ - пресметувањето продолжува.
- $p(|n|)^{sign(n)}$ за $n = -2$: $i' = p(2)^{-1} = 3^{-1}$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 96 \cdot i' = 32$.
- $p(|n|)^{sign(n)}$ за $n = 1$: $i' = p(1)^{1} = 2$. Бидејќи $i \cdot i' \in \mathbb{N}$, се поставува $i$ на $i \cdot i' = 32 \cdot i' = 64$.
- Сега $\frac{64}{3} \notin \mathbb{N}$, така што пресметувањето запира.

Така, $i$ сега е еднаков на $64 = 2^6$. Односно, вредноста од првиот регистар $p(1)$ и вредноста од вториот регистар $p(2)$ беа додадени и потоа зачувани во првиот регистар, $p(1)$. Општо земено, $E(2^a \cdot 3^b, ((2, -2, 1))) = 2^n$, со $n = a + b$.

### 4.3.2. Останати аритметички операции

Во овој дел ќе бидат покажани неколку примери за код на аритметички операции.

_Одземање_: $E(2^x \cdot 3^y, s_s) = 2^n \cdot 3^k$ каде $n = |x - y|$ и $k = 1$ ако $y > x$, и $k = 0$ во спротивно.
$$s_s = ((1, -1, 3, 5), (2, -2, 4, 6), (3, -3, -4), (6, -5, -6), (4, -4, 1, 3), (3, (3, -3), 2), (5, -5, 1))$$

_Множење_: $E(2^x \cdot 3^y, s_m) = 2^n$ каде $n = x \cdot y$.
$$s_m = ((1, -1, (2, -2, 3, 4), (4, -4, 2)), (2, -2), (3, -3, 1))$$

_Делење_: $E(2^a \cdot 3^d, s_d) = 2^q \cdot 3^r$ каде $a = qd + r$ и $0 \leq r < d$.
\begin{gather*}
s_d = ((2, -2, 7), (1, (7, -7, 2, 8), (8, -8, 7)) \doubleplus s_s \doubleplus \\ (9, (2, -2, (1, -1, -7), (7, -7, 8), -9)), (7, -7), (9, -9, 1), (8, -8, 2))
\end{gather*}

### 4.3.3. Композиција и интерпретација на програми

Како што се покажа со $s_d$, низите може да се композираат со нивно спојување:
$$\forall s_1, \forall s_2, E(E(i, s_1), s_2) = E(i, s_1 \doubleplus s_2)$$

На пример, низата $(1, 2, 2, (2, -2, 1))$ се состои од композирање на $(1, 2, 2)$ и $((2, -2, 1))$; прво се зголемуваат првиот и вториот регистер за 1 и 2 соодветно, а потоа се врши збир на регистрите, a резултатот се зачувува во првиот регистар. Псевдо-кодот на оваа низа може да се претстави на следниот начин, следејќи ја нејзината семантичка интерпретација:

```
r1 += 1; r2 += 2; // niza 1
while (r2 > 0) { r2 -= 1; r1 += 1; } // niza 2
// r1 += r2; r2 = 0; // niza 2 optimizirana
```

### 4.3.4. Аритметички операции (Python)

Со воведувањето на функциите од 4.3.2, следно може да се пресметаат неколку пример-програми во Budge-PL:

```
>>> arith_add = [[2, -2, 1]]
>>> get_registers(evaluate(set_registers({1: 4, 2: 5}), arith_add))
{1: 9}
>>> arith_sub = [[1, -1, 3, 5], [2, -2, 4, 6], [3, -3, -4], [6, -5, -6], [4, -4, 1, 3], [3, [3, -3], 2], [5, -5, 1]]
>>> get_registers(evaluate(set_registers({1: 5, 2: 3}), arith_sub))
{1: 2}
>>> get_registers(evaluate(set_registers({1: 3, 2: 5}), arith_sub))
{1: 2, 2: 1}
>>> arith_mul = [[1, -1, [2, -2, 3, 4], [4, -4, 2]], [2, -2], [3, -3, 1]]
>>> get_registers(evaluate(set_registers({1: 2, 2: 4}), arith_mul))
{1: 8}
>>> arith_div = [[2, -2, 7], [1, [7, -7, 2, 8], [8, -8, 7]] + arith_sub + [9, [2, -2, [1, -1, -7], [7, -7, 8], -9]], [7, -7], [9, -9, 1], [8, -8, 2]]
>>> get_registers(evaluate(set_registers({1: 4, 2: 2}), arith_div))
{1: 2}
>>> get_registers(evaluate(set_registers({1: 4, 2: 3}), arith_div))
{1: 1, 2: 1}
```

#### 4.3.4.1. Експоненти

Влез: $2^x \cdot 3^y$. Излез: $2^n$. Следниот код пресметува $x^y$ во $n$.

```python
arith_exp = [
  [2, -2, 5], # move r2 to r5
  [1, -1, 6], # set r6 to r1
  1,          # start with 1
  [5, -5,     # while y>0
    [6, -6, 7, 2], # set r7, r2 to r6
    [7, -7, 6]]    # bring r6 back
    + arith_mul,   # multiply
  [6, -6]]    # flush r6
```

Пример пресметка:

```
>>> get_registers(evaluate(set_registers({1: 2, 2: 3}, arith_exp)))
{1: 8}
```

#### 4.3.4.2. Фибоначиева низа

Влез: $2^x$. Излез: $2^n$. Следниот програм пресметува $Fib(x)$ во $n$.

```python
fib = [
  3,    # r1 = input/output, r2 = 0, r3 = 1, r4 = 0, r5 = 0
  [1,   # while n > 1
    -1,            # decrease n
    [3, -3, 2, 4], # move r3 to r4, and add it to r2
    [2, -2, 5],    # move r2 to r5
    [4, -4, 2],    # move r4 to r2, and add it to r2
    [5, -5, 3]],   # move r5 to r3
  [3, -3],    # flush r3
  [2, -2, 1]] # move r2 to r1
```

Пример пресметка:

```
>>> for i in range(0, 7):
...   print('Fib(%d) =' % i, get_registers(evaluate(set_registers({1: i}, fib))))
Fib(0) = {}
Fib(1) = {1: 1}
Fib(2) = {1: 1}
Fib(3) = {1: 2}
Fib(4) = {1: 3}
Fib(5) = {1: 5}
Fib(6) = {1: 8}
```

#### 4.3.4.3. Најголем заеднички делител

Влез: $2^x \cdot 3^y$. Излез: $2^n$. Го мести $n$ на $GCD(x, y)$.

```python
gcd = [
  [2,
    [2, -2, 11, 12], # copy b=r2 to r11, r12
    [12, -12, 2]]    # bring back b
    + arith_div +
    [[1, -1], [11, -11, 1]]] # set a = b
    # b is already remainder
```

Пример пресметка:

```
>>> get_registers(evaluate(set_registers({1: 2, 2: 4}, gcd)))
{1: 2}
>>> get_registers(evaluate(set_registers({1: 3, 2: 5}, gcd)))
{1: 1}
>>> get_registers(evaluate(set_registers({1: 12, 2: 16}, gcd)))
{1: 4}
```

#### 4.3.4.4. Проверка за прост број

Влез: $2^x$. Излез: $2^n$. Го мести $n$ на 1 ако $x$ е прост број, а на 0 во спротивно. Потребно е $x>1$.

```python
is_prime = [
  [1, -1, 11, 12],    # copy r1 to r11/r12
  [11,
    [12, -12, 1, 15], # first argument is original input
    [15, -15, 12],    # save original value from r15 (tmp) to r12
    [2, -2],
    [11, -11, 15],    # copy r11 to r15
    [15, -15, 2, 11]] # second argument is current iterator
    + arith_div +     # do the division
    [
    # if there was a non-zero remainder, increase r14 (no factors)
    [2, [2, -2], 14],
    -11,
    [1, -1]           # flush r1 (from division)
  ],
  [12, -12, 1],   # move r12 to r1 (total factors)
  [14, -14, -1],  # subtract r14 from r1 (total factors - no factors)
  # at this point, r1 contains the number of factors
  # if it's a prime, the number of factors will be two.
  -1, -1,         # if prime, r1 = 0, else r1 > 1
  # negate r1 for final result
  2, [1, -1, -2], [2, -2, 1]]
```

Идејата е да се зачува резултатот од `!(n%i)` во $r_{12}$, за `i=n;i>=0`. Се вели дека даден број е прост ако $r_{12}=2$, односно само два броја го делат тој број (1 и самиот број).

```
>>> for i in range(2, 10):
...   print('is_prime(%d) =' % i, get_registers(evaluate(set_registers({1: i}, is_prime))))
is_prime(2) = {1: 1}
is_prime(3) = {1: 1}
is_prime(4) = {}
is_prime(5) = {1: 1}
is_prime(6) = {}
is_prime(7) = {1: 1}
is_prime(8) = {}
is_prime(9) = {}
```

#### 4.3.4.5. Логаритам

Влез: $2^x \cdot 3^y$. Излез: $2^n$. Го мести $n$ на $log_y(x)$.

```python
logn = [
  [2, -2, 12], # store r2 to r12
  [1, # while the first argument is non-zero
    [2, -2],          # flush r2
    [15, -15],        # flush r15
    [12, -12, 2, 15], # restore r2 and save it to r3
    [15, -15, 12]]    # restore r12
    + arith_div +     # divide r1 by r2
    # negate r2 (see logical gate "Not")
    [[3, -3], 3, [2, -2, -3], [3, -3, 2],
    11,               # increase division count
  ],
  -11, # no off by one error
  [11, -11, 1], # flush r11 and move to r1
  [12, -12]]    # flush r12
```

Пример пресметка:

```
>>> for i in range(2, 9):
...   print('log2(%d) =' % i, get_registers(evaluate(set_registers({1: i, 2: 2}, logn))))
...   print('log3(%d) =' % (i+1), get_registers(evaluate(set_registers({1: i+1, 2: 3}, logn))))
log2(2) = {1: 1}
log3(3) = {1: 1}
log2(3) = {1: 1}
log3(4) = {1: 1}
log2(4) = {1: 2}
log3(5) = {1: 1}
log2(5) = {1: 2}
log3(6) = {1: 1}
log2(6) = {1: 2}
log3(7) = {1: 1}
log2(7) = {1: 2}
log3(8) = {1: 1}
log2(8) = {1: 3}
log3(9) = {1: 2}
```

#### 4.3.4.6. Логички порти

Логичките порти "негација", "и" и "или" се претставуваат со следниот код:

```python
logic_not = [2, [1, -1, -2], [2, -2, 1]]
logic_and = [[1, [1, -1], 3], [2, [2, -2], 3], -3, [3, -3, 1]]
logic_or = [[1, [1, -1], 3], [2, [2, -2], 3], [3, [3, -3], 1]]
```

Пример пресметки:

```
>>> for i in range(0, 3):
...   print('not %d = ' % i, get_registers(evaluate(set_registers({1: i}, logic_not))))
not 0 =  {1: 1}
not 1 =  {}
not 2 =  {}
>>> for i in range(0, 3):
...   for j in range(0, 3):
...     print('%d and %d =' % (i, j), get_registers(evaluate(set_registers({1: i, 2: j}, logic_and))))
0 and 0 = {}
0 and 1 = {}
0 and 2 = {}
1 and 0 = {}
1 and 1 = {1: 1}
1 and 2 = {1: 1}
2 and 0 = {}
2 and 1 = {1: 1}
2 and 2 = {1: 1}
>>> for i in range(0, 3):
...   for j in range(0, 3):
...     print('%d or %d =' % (i, j), get_registers(evaluate(set_registers({1: i, 2: j}, logic_or))))
0 or 0 = {}
0 or 1 = {1: 1}
0 or 2 = {1: 1}
1 or 0 = {1: 1}
1 or 1 = {1: 1}
1 or 2 = {1: 1}
2 or 0 = {1: 1}
2 or 1 = {1: 1}
2 or 2 = {1: 1}
```
