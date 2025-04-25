#import "simplepaper.typ": *

#show: project.with(
  title: "初等数学平均值和向量范数的关系",
  authors: (
    (
      name: "彭显哲",
      organization: [经济系2022本科班],
      email: "10214810424"
      ),
  ),
  abstract: "本文对于列向量求多种定义的平均值，检验它们与范数、半范数、拟范数定义的关系; 从定义出发，讨论了不同定义的平均值视为范数的可能性，也发现了一部分形式的平均值与范数的相似构造会怎样影响其用作距离度量的性质。未来的研究可以探索平均值在其他数学领域中的应用，以及它们在解决实际问题中的潜力。",
  keywords: (
    "矩阵分析基础",
    "范数三大公理",
    "平均值",
    "初等数学",
  ),
)

#let indent = h(2em)
#let ind = h(0.7em)
= 背景

以前我们在中小学的数学课中接触过多种定义的平均值，包括但不一定限于——算术平均、几何平均、平方平均、调和平均、对数平均，等等。同样地，也接触过特殊定义的$L_p dash.fig$范数，以及它和平均值的异同。学习到矩阵分析的基础知识#cite(<数学中基本空间的浅释>)和范数的更一般定义#cite(<向量的p-范数及向量序列的收敛性研究>)之后，我们就难免想知道：

模长的平均值可不可以也看作范数？考虑到中学阶段常常应用均值不等式与$L_p dash.fig$范数不等式的“反向”#cite(<关于正齐次不等式>)，它们的结构是否存在一些共通？
以下将对于列向量 $bold(x) = display(
  (x_1,x_2,x_3,···,x_n)^T
  )$
求多种定义的平均值，检验它们与范数、半范数、拟范数定义的关系。

= 正文 

== 概念回顾
\ \

根据本课程使用主教材#cite(<矩阵分析与应用>)，
以上三种定义即实函数
$f(bold(x)):V arrow RR,
forall
bold(x), bold(y) in V, c in KK$
（其中 $KK$ 表示 $RR$ 或 $CC$）
须满足以下条件：

#let qici = [
  $f(c bold(x)) = abs(c) dot.op f(bold(x))$\
  $(forall c in CC)$
  ]
#let zhengding = [
  $f(bold(x))>=0$\
        $f(bold(x))=0 
        arrow.l.r.double
        bold(x)=bold(0)$
  ] 
#let sanjiao = [
  $f(bold(x)+bold(y)) <= f(bold(x))+f(bold(y))$
  ]

#table(
  columns: (auto, auto, auto, auto),
  inset:(x:1.2em,y:1em),
  align: horizon,
  table.header([类型], [正定性], [齐次性],[三角不等式])
  )[范数][#zhengding][#qici][#sanjiao][
    半范数][
        $f(bold(x)) >= 0$\
        $bold(x) = bold(0) arrow.r.double f(bold(x)) = 0$\
        $f(bold(x)) = 0 arrow.r.double.not bold(x) = bold(0)$
      ][#qici][#sanjiao][
    拟范数
      ][#zhengding][#qici][
        $f(bold(x)+bold(y)) <= C(f(bold(x))+f(bold(y)))$\
        $(C in bold(R^+), C!=1)$
      ]

== 教材正文中“请读者自证”的两条概念结论

=== 命题内容
\

$||x||_p = (display(sum_(i=1)^m)
abs(x_i)^p)^(1/p)$ 在 $0<p<1$ 时是拟范数，在 $p>=1$ 时是范数。

=== 尝试解答
\

==== 正定性
\ \
$
cases(
p in RR^+,abs(x_i)>=0
)
#ind arrow.r.double #ind
    abs(x_i)^p&>=0
#ind arrow.r.double #ind
    display(sum_(i=1)^n) abs(x_i)^p&>=0
#ind arrow.r.double #ind
    (display(sum_(i=1)^n) abs(x_i)^p)^(1/p)&>=0
#ind arrow.r.double #ind
f(x)>=0 $\

以上不等号取等当且仅当： $abs(x_i)=0, forall i in {1,2,3,···,n}$ ，也即 $bold(x)=0$ ，故正定性得证。

==== 齐次性
\

$
f(c bold(x)) 
  &= (sum_(i=1)^n |c x_i|^display(p))^display(1/p)\
  &= (|c|^p sum_(i=1)^n |x_i|^p)^display(1/p)
  = |c| ^display(p dot.op 1/p)
  (sum_(i=1)^n |x_i|^p) ^display(1/p)
  = |c|(sum_(i=1)^n |x_i|^p)^(1/p)\ \ 
  &=|c|f(bold(x))
$

==== 三角不等式
\ 

===== $p=1$ 时
\ \ 

$
f(bold(x)+bold(y)) #ind
= #ind sum_(i=1)^n |x_i+y_i|#ind 
<= #ind sum_(i=1)^n (|x_i| + |y_i|)#ind
<= #ind sum_(i=1)^n |x_i| + sum_(i=1)^n |y_i|#ind
= #ind f(bold(x))+f(bold(y))
$
#pagebreak()
===== Young不等式
\ \

若 $p,q in RR, #ind p>1, #ind q>1, 
    #ind display(
      1/p+1/q=1
    )$ ，则有
$
\
  |x y| <= (|x|^p)/p + (|y|^q)/q#indent
   forall x, y in RR
$
证明（作商法）：

$(1)$ 当 $x y=0$ 时，不妨设 $y=0$ ，
      $display(0<= (|x|^p)/p)$ 显然成立；

$(2)$ 当 $x y != 0$ 时，构造函数
  $
    display(g(t)&= t^p/p + t^(-q)/q)
    #indent (t in RR^+)\ \
  
    arrow.r.double#ind
    (diff g)/(diff t)
    &= p dot t^(p-1)/p + (-q) dot t^(-q-1)/(q)\ \
    &= t^(p-1) - t^(-(q+1))
    = t^(p-1) - 1/(t^(q+1))\ \

    arrow.r.double#ind
    (diff^2 g)/(diff t^2)
    &= (p-1)t^(p-2)-(-q-1)t^(-q-2)\
    &= (p-1)t^(p-2)+(q+1)dot 1/t^(q+2)>0\ \

    arrow.r.double#ind
    (diff g)/(diff t)|_(t=1) 
    &= 1^(p-1)-1/1^(q+1)\
    &=1-1\
    &=0\
    #indent
    &arrow.r.double
    #indent
    cases(
    display((diff g)/(diff t)|_(t<1)<0),
    "",
    display((diff g)/(diff t)|_(t>1)>0)
    )\ \

    arrow.r.double#ind
    min_t {g(t)}&=g(1)\
    &=1^p/p+1^(-q)/q\
    &=1/p+1/q=1\ \

    &arrow.r.double#ind
    g(t)>=min_t {g(t)}=1\ \

    &arrow.r.double#ind
    t^p/p + t^(-q)/q >= 1

$
\
\
\
\
\
\
$
    display((|x|^p)/p + (|y|^q)/q)/(|x y|)
    #ind &=#ind display((|x|^(p/q+1))/p + (|y|^(q/p+1))/q)/(|x y|)

    #indent#ind
    arrow.l.double.long 
    #indent#ind

    
    1/p+1/q=1 arrow.r.double p+q=p q 
    arrow.r.double cases(
        display(p=p/q+1), 
        display(q=q/p+1)
      )
    
    \ \

    &=#ind 1/p (|x|^(p/q+1))/(|x y|) + 
      1/q (|y|^(q/p+1))/(|x y|)
    \ \
    &=#ind 1/p (|x|^(p/q)|x|)/(|x|dot|y|) + 
      1/q (|y|^(q/p)|y|)/(|x|dot|y|)
    \ \
    &=#ind 1/p (|x|^(p/q))/(|y|) + 
      1/q (|y|^(q/p))/(|x|)
    \ \
    &=#ind 
      1/p ((|x|^(1/q))/(|y|^(1/p)))^p + 
      1/q ((|y|^(1/p))/(|x|^(1/q)))^q
      #ind
    \ \
    &=#ind
      1/p ((|x|^(1/q))/(|y|^(1/p)))^p + 
      1/q ((|x|^(1/q))/(|y|^(1/p)))^(-q)
    \ \
    &=#ind
    g((|x|^(1/q))/(|y|^(1/p)))>=1
    \ \

    &arrow.r.double #ind
    (|x|^p)/p + (|y|^q)/q >= |x y|\ \
    #ind &arrow.r.double #ind
    |x y| <= (|x|^p)/p + (|y|^q)/q
  $
#pagebreak()
===== Hölder不等式
\ \

若 $p, q, r in bold(RR^+),#ind p>1,#ind q>1,#ind 
display(1/p+1/q=1)$ ，则有
  $
    sum_(i=1)^n |x_i|dot|y_i|
    <=(sum_(i=1)^n |x_i|^p)^(1/p)
      (sum_(i=1)^n |y_i|^q)^(1/q)#indent 
      forall x_i, y_i in CC,
      #indent i in {1,2,3,···,n}
  $

  $
    (display(sum_(i=1)^n) |x_i|dot|y_i|)/(
      (display(sum_(i=1)^n) |x_i|^p)^(1/p)
      (display(sum_(i=1)^n) |y_i|^q)^(1/q)
    )
    #ind &=#ind sum_(i=1)^n ((|x_i|)/(
      (display(sum_(i=1)^n) |x_i|^p)^(1/p))
      dot
      (|y_i|)/((display(sum_(i=1)^n) |y_i|^q)^(1/q)))
    \ \
    #ind &=#ind sum_(i=1)^n abs((|x_i|)/(
      (display(sum_(i=1)^n) |x_i|^p)^(1/p))
      )abs(
      (|y_i|)/((display(sum_(i=1)^n) |y_i|^q)^(1/q)))
    \ \ \

    #ind &<=#ind sum_(i=1)^n {abs((|x_i|)/(
      (display(sum_(i=1)^n) |x_i|^p)^(1/p))
      )^p/p
      +abs(
      (|y_i|)/((display(sum_(i=1)^n) |y_i|^q)^(1/q)))^q/q
      }
      arrow.l.double
      |x y| <= (|x|^p)/p + (|y|^q)/q
    \ \ \
    #ind &=#ind sum_(i=1)^n {
      (|x_i|^p)/
      (p abs(display(sum_(i=1)^n) |x_i|^p))
      +
      (|y_i|^q)/
      (q abs(display(sum_(i=1)^n) |y_i|^q))
    }\ \ \ 
    #ind &= #ind (display(sum_(i=1)^n) |x_i|^p)/
      (p abs(display(sum_(i=1)^n) |x_i|^p))
      +
      (display(sum_(i=1)^n) |y_i|^q)/
      (q abs(display(sum_(i=1)^n) |y_i|^q))
    \ \ \

    #ind &=#ind 1/p+1/q#ind =#ind 1 #indent
    
    arrow.r.double#indent
    sum_(i=1)^n |x_i|dot|y_i|
    <=(sum_(i=1)^n |x_i|^p)^(1/p)
      (sum_(i=1)^n |y_i|^q)^(1/q)
  $

===== $p>1$ 时
\ \

设 $ q in RR^+$ 满足 $display(1/p+1/q=1)$ 则有
  $
  
    1/q=1-1/p #ind arrow.r.double #ind
    cases(
      display(1-1/q=1/p),
      "", 
      "",
      display(q=1/display(1-1/p)=p/(p-1)
      #ind arrow.r.double #ind
      q(p-1)=p)
    )
  $

$
  sum_(i=1)^n |x_i+y_i|^p
  &=#ind sum_(i=1)^n |x_i+y_i|^(p-1)dot|x_i+y_i|
  \
  &<=#ind sum_(i=1)^n |x_i+y_i|^(p-1)(|x_i|+|y_i|)
  \
  &=#ind sum_(i=1)^n |x_i+y_i|^(p-1)|x_i|+sum_(i=1)^n |x_i+y_i|^(p-1)|y_i|
  \
  &=#ind sum_(i=1)^n |x_i|dot|(x_i+y_i)^(p-1)|+sum_(i=1)^n |y_i|dot|(x_i+y_i)^(p-1)|
  \
  &<=#ind (sum_(i=1)^n abs(x_i)^p)^(1/p)
     (sum_(i=1)^n abs((x_i+y_i)^(p-1))^q)^(1/q)
    +
     (sum_(i=1)^n abs(y_i)^p)^(1/p)
     (sum_(i=1)^n abs((x_i+y_i)^(p-1))^q)^(1/q) 
  \ \
  &=#ind (sum_(i=1)^n abs(x_i+y_i)^(q(p-1)))^(1/q)
    (
      (sum_(i=1)^n abs(x_i)^p)^(1/p)
      +
      (sum_(i=1)^n abs(y_i)^p)^(1/p)
    )
  \ \
  &=#ind (sum_(i=1)^n abs(x_i+y_i)^p)^(1/q)
    (
      (sum_(i=1)^n abs(x_i)^p)^(1/p)
      +
      (sum_(i=1)^n abs(y_i)^p)^(1/p)
    )
  \ \
  &arrow.r.double#ind
  sum_(i=1)^n |x_i+y_i|^p
  <=(sum_(i=1)^n abs(x_i+y_i)^p)^(1/q)
    (
      (sum_(i=1)^n abs(x_i)^p)^(1/p)
      +
      (sum_(i=1)^n abs(y_i)^p)^(1/p)
    )
$

$
  arrow.r.double
  (sum_(i=1)^n |x_i+y_i|^p)^(1-1/q)
  &<=(sum_(i=1)^n abs(x_i)^p)^(1/p)
    +
    (sum_(i=1)^n abs(y_i)^p)^(1/p)
  \ \ 
  arrow.r.double
  (sum_(i=1)^n |x_i+y_i|^p)^(1/p)
  &<=(sum_(i=1)^n abs(x_i)^p)^(1/p)
    +
    (sum_(i=1)^n abs(y_i)^p)^(1/p)
  \ \ \
  arrow.r.double
  f(bold(x)+bold(y))&<=f(bold(x))+f(bold(y))
$

#pagebreak()
== “次数型”均值常见特例
\

=== 算术平均（Arithmetic Mean）
\ \

对于列向量 $bold(x)$ 求模长的算术平均值有
$
  A\M(bold(x))=1/n display(sum_(i=1)^n) |x_i|
$

=== 平方平均（Root Mean Square）
\ \

对于列向量 $bold(x)$ 求模长的平方平均值有
$
  R\M(bold(x)) = sqrt(1/n display(sum_(i=1)^n)
  |x_i|^2)
$

=== 调和平均（Harmonious Mean）
\ \

对于列向量 $bold(x)$ 求模长的调和平均值有
$
  H\M (bold(x)) =
    display(n)/(display(sum_(i=1)^n) 
    display(abs(1/x_i)))
$

== “次数型”一般情形
\ \

$
  f(bold(x))
  =((
    display(sum_(i=1)^n)
    |x_i|^p)/n
    )^(1/p)
$

=== 正定性
\

$f(bold(x))>=0$ 总是成立，但需验证取零的等价关系。

$f(bold(x))=0 
arrow.r.double 
display(sum_(i=1)^n)
    |x_i|^p=0$ 又 $|x_i|>=0 
    arrow.r.double bold(x)=bold(0)$

    反之是平凡的。


=== 齐次性
\ 
$
  f(c bold(x))
  =((sum_(i=1)^n |c x_i|^p)/n)^(1/p)
  =((|c|^p sum_(i=1)^n |x_i|^p)/ n)^(1/p)
  =|c|((sum_(i=1)^n |x_i|^p)/n)^(1/p)
  =|c|f(bold(x))
$
#pagebreak()

=== 三角不等式
\ \

需验证
$
((sum_(i=1)^n |x_i+y_i|^p)/n)^(1/p)
  &<=((sum_(i=1)^n abs(x_i)^p)/n)^(1/p)
    +
    ((sum_(i=1)^n abs(y_i)^p)/n)^(1/p)
  \ \

  arrow.l.r.double#ind
    (1/n)^(1/p)(sum_(i=1)^n |x_i+y_i|^p)^(1/p)
  &<=(1/n)^(1/p)(sum_(i=1)^n abs(x_i)^p)^(1/p)
    +
    (1/n)^(1/p)(sum_(i=1)^n abs(y_i)^p)^(1/p)
  \ \
  arrow.l.r.double#ind
    (sum_(i=1)^n |x_i+y_i|^p)^(1/p)
  &<=(sum_(i=1)^n abs(x_i)^p)^(1/p)
    +
    (sum_(i=1)^n abs(y_i)^p)^(1/p)
$\

这个不等式在前文已证明 $p>1$ 时的情况。

== 其他常见特例
\ 

=== 几何平均（Geometric Mean）
\ \

对于列向量 $bold(x)$ 求模长的平方平均值有
$
  G\M(bold(x)) = (
    display(product_(i=1)^n) 
  display(abs(x_i))
  )^display(1/n)
$

==== 正定性
\ \

若有一 $x_i=0$ ，则无论其余元素情况，总有 $G\M=0$ ——
该函数具有半正定性。

==== 齐次性
\ 
$
f(c bold(x))&=(
    display(product_(i=1)^n) 
  display(abs(c x_i))
  )^display(1/n)
  =(
    display(|c|^n product_(i=1)^n) 
  display(abs(x_i))
  )^display(1/n)
  =|c|(
    display(product_(i=1)^n) 
  display(abs(x_i))
  )^display(1/n)
  =|c|f(bold(x))
$
#pagebreak()
==== 三角不等式
\ \

考虑这样两个向量$
bold(x)=vec(3,2,3)#indent 
bold(y)=vec(1,4,3)#indent#indent
cases(
    f(bold(x))&tilde.equiv 2.62,
    f(bold(y))&tilde.equiv 2.29,
    f(bold(x)+bold(y))&tilde.equiv 5.24
  )\ \
f(bold(x))+f(bold(y))-f(bold(x)+bold(y))
tilde.equiv-0.33<=0 arrow.r.double
f(bold(x))+f(bold(y))<f(bold(x)+bold(y))
$\

模长的几何平均值与三角不等式条件冲突。

=== 对数平均（Logarithmic Mean）
\ \

对于列向量 $display(bold(x)=vec(x_1,x_2))$ 求模长的对数平均值有
$
L\M(bold(x)) = cases(
    #ind display(|x_1| " " = " " |x_2|)
    &(|x_1|=|x_2|),
    "",
    display((|x_1|-|x_2|)/(ln |x_1| - ln |x_2|))
    #indent#indent#indent
    &(|x_1|!=|x_2|)
    )
$

==== 正定性
\ \

由于自然对数在$RR^+$单调递增，$f(bold(x))>=0$ 总是成立。$bold(x)=bold(0)$ 在该函数上无定义。

==== 齐次性
\ \
$
f(c bold(x))&=
(|c x_1|-|c x_2|)/(ln|c x_1|-ln|c x_2|)\ \
&=(|c|(|x_1|-|x_2|))/(ln|c|+ln|x_1|-ln|c|-ln|x_2|)\ \
&=|c|(|x_1|-|x_2|)/(ln|x_1|-ln|x_2|)
=|c|f(bold(x))
$
#pagebreak()
==== 三角不等式
\ \

考虑这样两个向量$
bold(x)=vec(3,7)#indent 
bold(y)=vec(1,15)#indent#indent
cases(
    f(bold(x))&tilde.equiv 4.72,
    f(bold(y))&tilde.equiv 5.17,
    f(bold(x)+bold(y))&tilde.equiv 10.56
  )\ \
f(bold(x))+f(bold(y))-f(bold(x)+bold(y))
tilde.equiv-0.67<=0 arrow.r.double
f(bold(x))+f(bold(y))<f(bold(x)+bold(y))
$\

模长的对数平均值与三角不等式条件冲突。

== 图象观察
\ \

对于次数型均值表达式 $display(
  (1/n (sum_(i=1)^n |x_i|^p))^(1/p)
  )$\ \

  分别取 $p =$ 
  $100, 3, 2, 1, 
  display(1/2), display(1/3), display(-1/100),-1$,
  在 $n=2$ 的特殊情况下在二维平面作图显示：\

 #figure(image("desmos-graph.svg"),
  caption: [
    用 $x$ 和 $y$ 作向量元素，各均值等于 $1$ 的图象
  ],
)<img>

  图象随着 $p$ 的减小，逐渐远离原点。全部图象切于
  $abs(x)=1,#ind abs(y)=1$ 处。当 $p>0$ 时，图象封闭；当 $p<0$ 时，图象以坐标轴为渐近线，伸向无穷远处。这辅助说明了 $p<0$ 时，次数型均值既不是范数，也不是拟范数或半范数的结论。
  
  $p>1$时，图象是凸集；$p<1$时，图象不是凸集。

  几何平均值等于一的图象在 $p=-"1/100"$ 图象的内侧，但非常贴近——这能够显示中学老师“可以把几何均值当成零次均值”论断的某种合理性；对数平均值等于一的图象在 $p="1/3"$ 图象的内侧，但非常贴近——这说明对数平均值是比几何平均“次数更大”的“零次平均”。

= 总结与展望
\ 

平均值在特定条件下可以被视为范数或拟范数，但并非所有情况下都满足范数的全部性质。一个特别的例子是，几何平均和对数平均在某些情况下与三角不等式的要求相悖。

在前文基础上，我们还可以将平均值和范数的关系讨论得更加深入，不仅对基础教育阶段的课堂内容有好处，也对机器学习和运筹优化算法改进有潜在的启发。

#bibliography("ref.bib")
