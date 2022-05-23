# upd: 2022-5-13

Logic.v 最后一个证明excluded_middle, peirce, double_negation_elimination, de_morgan_not_and_not, implies_to_or互相等价是一个5stars的练习，目前我还没找到网上有人写这个。我想了两三天写出来了，真是精彩。

# upd:2022-5-21

IndProp.v后面的附加题真是一个比一个难==

犯了个错误：

```

(forall x : X, In x l1 -> In x l2)
```

这句话不是“l1是l2的子序列”的意思

哦还有官网上说Coq8.12后不支持使用omega tatic了。取而代之的是Coq.micromega.Lia.

# update: 2022-5-23

发现我在Induction Hypothesis的时候，总是会发现有效信息丢失。

于是我就有了以下奇怪的操作：

```

assert (H的内容) { apply H. }
induction H.
```

这样的话就会出现一个H'=H的内容，然后再induction H时就会多信息了。

同理还有如果我想destruct (b : bool)后，Hypothesis里有个b=true，

那么我会写

```

remember b as b1.
destruct b1.
- // 这里就有b=true了
```

