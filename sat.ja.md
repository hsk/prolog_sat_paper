# A Pearl on SAT Solving in Prolog

Jacob M. Howe1 and Andy King2

1 Department of Computing, City University London, EC1V 0HB, UK

2 School of Computing, University of Kent, CT2 7NF, UK

## 概要

遅延宣言による制御を利用し、ウォッチドリテラルと単位伝搬を実装した簡潔なSATソルバーを紹介する。
その簡潔さにもかかわらず、このソルバーは驚くほど強力であり、Prologの構成要素をエレガントに使用した、プログラミングの真髄が示されている。
## 1 Introduction はじめに

ブール充足可能性問題（SAT）は、様々な問題がSATインスタンスとして自然に表現可能であるため、継続的な関心を集めている。
効率的なSATソルバーのアルゴリズムや実装の開発には多くの努力が払われてきた。
その結果、特殊なアプリケーションや汎用的なソルバーが数多く開発されている[5]。

最近、Cでコード化された専用の外部SATソルバをPrologと統合する方法が示され [2]、これは多くのアプリケーションに利用されている。
この研究は、論理式を接続正規形(CNF)に変換するために、Prologをエレガントに使用することで、真珠として発表された。
この研究は、SATソルバーをコーディングする媒体としてPrologが適しているかという疑問を投げかけた。
この短い論文では、SATソルバーがPrologでコード化できるだけでなく、このソルバーがいわゆるナチュラルパールであることを論じる。
すなわち、効率的なSAT解法の主要概念は、パラダイムの核心にある論理と制御機能[11]の組合せを用いて、論理プログラムで定式化することができる。
この真珠は、論理変数を用いたブール関数の表現から自然に生まれた効率的な基底解析器[8]を実装する際に発見された。

このパールで例証されている論理と制御の特徴は、論理変数の使用、バックトラック、遅延宣言による実行の中断と再開である[15]。
遅延宣言とは、ある条件が満たされるまで、ゴール内のアトムの選択を遅らせる方法を提供する制御メカニズムである。
遅延宣言は、例えば、否定されたゴールや非線形制約を扱う方法を提供する。
遅延宣言は、Prologシステムには不可欠なものであるが、このパラダイ ムにおけるその重要性は、最近になって正式に確立された[10]。
この論文では、Davis, Putnam, Logemann, Loveland (DPLL)アルゴリズム[3]をwatched リテラル[14]で実装することで、PrologとSATのマッチングがいかに良いかを示す。
ウォッチドリテラルは、SATソルバーを高速化する最も強力な機能の一つである。
得られたソルバーは、エレガントで簡潔であり、20行のPrologでコードされ、自己完結的であり、いくつかの興味深い、控えめではあるが、SATインスタンス[8, 9]を解くのに十分効率的であることが議論される。
このソルバーは、様々な方法でさらに発展させることができる。
本稿の残りの部分では、SAT解法に関連する背景を短く要約し、ソルバーのコードを示し、それについてコメントし、その力を実証するために短い経験的評価を示し、ソルバーの拡張について議論し、ソルバーとそのアプローチの限界について議論して終わる。

```
(1)  function DPLL(f : CNF formula, θ : truth assignment)
(2)  begin
(3)      θ1 := θ ∪ unit-propagation(f , θ);
(4)      if (is-satisfied(f , θ1)) then
(5)          return θ1;
(6)      else if (is-conflicting(f , θ1)) then
(7)          return ⊥;
(8)      endif
(9)      x := choose-free-variable(f , θ1);
(10)     θ2 := DPLL(f , θ1 ∪ {x 7 → true});
(11)     if (θ2 6 = ⊥) then
(12)         return θ2;
(13)     else
(14)         return DPLL(f , θ1 ∪ {x 7 → f alse});
(15)     endif
(16) end
```

図1. DPLLアルゴリズムの再帰的定式化
## 2 Background 背景

本節では、SAT問題と、ソルバーが実装するウォッチド・リテラルを用いた DPLLアルゴリズム[14]について簡単に概説する。

ブール充足可能性問題とは、与えられたブール式に対して、その式が真と評価されるような真理値代入が変数に存在するかどうかを決定する問題である。
最近のブール充足可能性ソルバーのほとんどは、Davis, Putnam, Logemann, Loveland (DPLL)アルゴリズム[3]に基づいている。
図1は、[16]に示されているアルゴリズムに基づく再帰的な定式化である。
関数DPLLの最初の引数は、命題変数Xの集合上で定義された式fである。
通常、fはCNFであると仮定する。
第2引数のθは、X→{true, f alse}上の部分（真理）関数である。
DPLL(f、φ)の呼び出しは、φが空の真理関数を表すfの充足可能性を決定する。
呼び出しが特別な記号⊥を返した場合、fは不成立であり、そうでない場合、 呼び出しはfを満たす真理関数θを返す。
## 2.1 Unit propagation 単位伝播

(3)行目では、fとθにいわゆる単位伝搬を適用することで、真理値代入θをθ1に拡張する。
例えば、f = (¬x ∨ z) ∧ (u ∨ ¬v ∨ w) ∧ (¬w ∨ y ∨ ¬z)で、X = {u, v, w, x, y, z}、θは部分関数θ = {x 7 → true, y 7 → f alse}であるとする。
単位伝播はfの各節を調べ、θを拡張し、fが充足可能であるために必然的に成り立つ真理値代入θ1を推論する。
例えば、(¬x ∨ z)という節が充足可能であり、したがってf全体として充足可能であるためには、z 7 →真であることが必要である。
さらに、(¬w ∨ y ∨ ¬z)が充足可能であるためには、w 7 → f alse が成り立つ。
(u∨¬v∨w)の充足可能性は、uとvの2つの未知数に依存する。
関数unit-propagation(f, θ)はこの推論をカプセル化し、束縛{w 7 → f alse, z 7 → true}を返す。
θをこれらの必要な結合で拡張するとθ1が得られる。
## 2.2 Watched literals 監視されたリテラル

ある節から情報が得られるのは、その節が2つの未知数を含まない場合だけである。
これは、unit propagationを実現するための実装技術であるwatched literals [14]の背後にある観察である。
この考え方は、2つの未知数のみを監視することで、節を監視し続けることである。先ほどの例に戻ると、変数代入が行われる前に、(u ∨ ¬v ∨ w)節に適したモニターは未知数のuとvであり、(¬w ∨ y ∨ ¬z)節に適したモニターはwとzであり、(¬x ∨ z)節にはxとzのモニターが必要である。
最初の空θがx 7 →真で補強されるとき、第3節の新しいモニターは利用できず、単位伝播は直ちにz 7 →真を推論するために適用される。
zの新しい束縛は2番目の節のモニターによって検出され、モニターはwとyに更新される。
θがさらにy 7 → f alseで補強されると、yの変化は再び(¬w ∨ y ∨ ¬z)のモニターによって検出される。このとき、監視する未束縛の変数は残っておらず、単位伝搬が適用され、束縛 w 7 → f alse が得られる。
したがって、ウォッチド・リテラ ルは、節を不必要に検査することなく伝搬を制御するメカニズムを提供する。
## Termination and the base cases 2.3 終了と基本ケース

単位伝搬が完全に適用されたら、あとはfが充足可能であるために十分な変数が束縛されているかどうかを検出する。
これがis-satisfied(f, θ)という述語の役割である。この述語は、fのすべての節に少なくとも1つの充足されるリテラルが含まれていれば真を返す。例えば、is-satisfied(f, θ1)=falseは、(u ∨ ¬v ∨ w)はθ1の下では満たされない。もしis-satisfied(f, θ1)が満足されるなら、θ1は満足する割り当ての存在を証明するために返されるかもしれない。

逆に、fとθ1を検査すると矛盾が観察され、そこからfは不成立であることが導かれる。
例として、f = (¬x) ∧ (x ∨ y) ∧ (¬y)、θ = ∅とする。
第1節と第3節から、θ1 = {x 7 → f alse, y 7 → f alse}となる。
is-conflicting(f,θ)という述語は、fにすべてのリテラルが満足できない節が含まれているかどうかを検出する。(x∨y)節はθ1のもとでこの条件を満たすので、fは⊥を返すことでunsatisfiableであることが示される。

```prolog
sat(Clauses, Vars) :-
    problem_setup(Clauses), elim_var(Vars).

elim_var([]).
elim_var([Var | Vars]) :-
    elim_var(Vars), (Var = true; Var = false).

problem_setup([]).
problem_setup([Clause | Clauses]) :-
    clause_setup(Clause),
    problem_setup(Clauses).

clause_setup([Pol-Var | Pairs]) :- set_watch(Pairs, Var, Pol).

set_watch([], Var, Pol) :- Var = Pol.
set_watch([Pol2-Var2 | Pairs], Var1, Pol1):-
    watch(Var1, Pol1, Var2, Pol2, Pairs).

:- block watch(-, ?, -, ?, ?).
watch(Var1, Pol1, Var2, Pol2, Pairs) :-
    nonvar(Var1) ->
        update_watch(Var1, Pol1, Var2, Pol2, Pairs);
        update_watch(Var2, Pol2, Var1, Pol1, Pairs).
update_watch(Var1, Pol1, Var2, Pol2, Pairs) :-
    Var1 == Pol1 -> true; set_watch(Pairs, Var2, Pol2).
```

図2. SATソルバーのコード
## 2.4 Search and the recursive cases 探索と再帰的ケース

満足可能性も不満足可能性も検出されなかった場合、変数xがラベリング用に選択される。そして、DPLLアルゴリズムがθ1に新しい結合x 7 →真を追加して起動される。
この選択で充足可能性が検出できない場合、DPLLはx 7 → f alseで拡張されたθ1で起動される。
再帰呼び出しのたびに未割り当て変数の数が厳密に減るので、終了は確実である。
## 3 The SAT Solver SATソルバー

ソルバーのコードを図2に示す。わずか20行のPrologで構成されている。
代入と伝播の宣言的記述はPrologで完全に表現できるので、実行は探索を制御するすべての側面を扱うことができ、図に示す簡潔なコードになる。
## 3.1 Invoking the solver ソルバーの起動

ソルバーは2つの引数で呼び出される。最初の引数はCNFの式をリストのリストとして表し、各リストは節を表す。
節のリテラルは Pol-Var のペアで表現され、Var は論理変数、Pol はリテラルが正または負の極性を持つことを示す真または偽である。
式¬x ∨ (y ∧ ¬z)は、CNFでは(¬x ∨ y) ∧ (¬x ∨ ¬z)と表現され、ソルバーにはリストL = [[false-X, true-Y], [false-X, false-Z]]として表示される。
2番目の引数は、問題に現れる変数のリストである。したがって、クエリsat(L, [X, Y, Z])は成功し、例えばX = false, Y = true, Z = trueのように変数を解に束縛する。
副産物として、Lは[[false-false, true-true], [false-false, false-true]]にインスタンス化される。これは、Lにおけるtrueとfalseの解釈が、-演算子の左か右かに依存することを示している：左では極性を表し、右では真理値を表す。
Lが満足できない場合、sat(L, Vars)は失敗する。必要であれば、二重否定の下でソルバーを呼び出し、変数を束縛しないまま、充足可能性をチェックすることができます。
## 3.2 Watched literals 監視されるリテラル

このソルバーは、各節の2つのリテラルを監視するウォッチゴールを起動することに基づいている。リテラルの極性は既知であるため、これは節に現れる2つのインスタンス化されていない変数の1つが束縛されるまで実行をブロックすることになる。従って、ウォッチ述語は、その第1引数と第3引数の一方が真理値 にインスタンス化されるまでブロックする。
SICStus Prologでは、この要求は、宣言 :- block watch(-, ?, -, ?, ?) によって記述される。
最初の引数が束縛されている場合、update watchは、束縛された変数の極性とその束縛に基づいて、もしあれば、どのようなアクションを実行するかを診断する。
極性が正で、変数が真にバインドされていれば、節は満たされ、それ以上のアクションは必要ない。同様に、変数が偽で極性が負であれば、節は満たされる。
それ以外の場合、節の充足可能性は、まだ検査されていない節の変数に依存する。
それらは、後続のset watch呼び出しで考慮される。
## 3.3 Unit propagation 単位伝播

セットウォッチの最初の節は、ウォッチする変数がない場合の処理である。
残りの変数が束縛されていない場合、単位伝搬が起こり、その変数に節を満たす値が代入される。
変数の極性が正の場合、その変数には真が代入される。
逆に極性が負であれば、その変数には偽が代入される。
両方のケースに対応するには、1つの単一化で十分である。
VarとPolが単一化可能でない場合、Varsへのバインディングは節を満たさないので、CNF式全体を満たさない。

problem_setup(Clauses)がリストClausesの各節のプロセスを起動すると、elim var(Vars)が呼び出され、Varsの各変数を真理値にバインドする。
第1引数か第3引数がバインドされると、制御はウォッチゴールに切り替わる。
事実上、elim vars(Vars)の(Var = true; Var = false)サブゴールは、problem setup(Clauses)のウォッチサブゴールとコルーチンする。
従って、例えば、elim var(Vars)は変数をバインドすることができ、その変数を待っているウォッチゴールに制御を移すことができる。
このゴールは、update watchを呼び出し、set watchを起動することができる。ユニット伝搬は別の変数をインスタンス化することができるので、制御は別のウォッチゴールに渡され、elim vars(Vars)の1つのバインディングから一連のバインディングが発生する。
制御がelim var(Vars)に戻るのは、単位伝搬が最大に適用されたときだけである。
## 3.4 Search 検索

コルーチニングをサポートすることに加えて、Prologは、バックト ラッキングによって、衝突するバインディングを取り消すことができる。
例えば、elim var(Vars)の1つのバインディングが、ウォッチゴールによる一連のバインディングの引き金となり、その際、ウォッチゴールが衝突に遭遇したとします。
そして、バックトラックは、elim var(Vars)で作られた元のバインディングと、ウォッチゴールによって作られたその後のバインディングを元に戻す。
ウォッチゴール自体も、elim var(Vars)で元のバインディングが行われた直前の実行時点まで巻き戻される。
elim var(Vars)はVarsを次の真理値の組み合わせにインスタンス化する。
このように、監視、伝播、探索はシームレスに織り込まれている。

バックトラックは、ほとんどのSATソルバーとは異なり、すべての満足する代入を列挙することができることに注意してください（したがって、[2]も）。
例えば、問い合わせsat(L, [X, Y, Z])は解を与える：

```
    X = false, Y = true, Z = true; X = false, Y = false, Z = true;
    X = true, Y = true, Z = false; X = false, Y = true, Z = false;

and X = false, Y = false, Z = false.
```
## 4 Extensions 拡張

過去10年間のSATソルバーの開発により、汎用ソルバーの性能を劇的に向上させる 数多くのヒューリスティックが生み出されてきた。
本節では、このような改良の数々を上記のソルバーにどのように組み込むかを概説する。
ただし、一般的な学習ヒューリスティック[13]については、ソルバーへの組み込みがより問題となるため、セクション6まで議論を残す。

- 最初の最も単純なヒューリスティックは、静的な変数順序を用いることである。変数は入力問題での出現頻度順に並べられ、最も出現頻度の高いものが最初に割り当てられる。
これは2つの点で有利である。すなわち、節を満たすことで問題サイズが素早く縮小し、達成される伝播量が大きくなる。
どちらも、満足する割り当てまたは競合に到達するために必要な割り当ての数を減らす。
もちろん、この戦術はPrologで簡単に実装できる。
- 静的変数順序付けは、問題の構造を発見し利用することを目的とした、最も単純な前処理戦術である。
問題の構造を分析するだけでなく、もう一つのよく使われる戦術は、解決ステップの限定されたアプリケーションを使用して問題を再構築することによって問題を変更することです[4]。
ここでも、これらの前処理ステップは、Prologで十分に達成することができます。
- 多くのSATソルバは、探索木の実りのない枝の探索を避けるために、非同期バックトラック、またはバックジャンプを使用する[13]。
Prologの深さ優先探索アルゴリズムのためのバックジャンプは、 [1]で研究されており、このアプローチは、この論文で紹介されるソルバーにも引き継がれる。
- 探索中に変数を動的に並べ替える方法[14]も、SATソルバーに広く取り入れられている。
これも本稿で紹介するソルバーに組み込むことができる。
このアプローチは[1]のバックジャンピングと類似しており、黒板を使用して競合情報を保持し、バックトラック後に次の変数を選択するために使用される。
## 5 Experimental Results 実験結果

ソルバーが取り組むことができる問題を説明するために、小規模なベンチマーク・スイートの実験結果を以下に示す。
表中、benchmarkはSATインスタンス名、varsとclausesはそれぞれ変数と節の数、satisfiableはインスタンスが充足可能かどうか、timeは最初に充足する代入を見つける、またはそのような代入が存在しないことを証明するのにかかった時間、miniはMiniSatを使用したベンチマークの時間、assignsはelim varで行われた変数代入の総数を示す。
MiniSatの結果は参考のために含まれており、C実装と多くのヒューリスティックの使用により、驚くなかれかなり高速である。
また、SICStusのタイミング粒度はMiniSatとは異なることに注意されたい。
実装はSICStus 4.0.4で、これらの実験は2.4GHz Intel Core 2 Duoプロセッサと4GBのメモリを搭載したMacBookのシングルコアで実行された。
タイムアウトは1分に設定した。最後に、これらの結果はセクション4で説明したように静的変数順序を利用しており、これによりこれらのベンチマークのソルバーが大幅に高速化されていることに注意されたい。

最初の6つのchat_80ベンチマークは、[8]のPosベース解析で解かれた最大のSATインスタンスの選択である。
これらは、fixpoint計算の安定性をチェックするための含意チェックを符号化したものであり、それ自体は必ずしも正ブール式（定義により充足可能）ではないことを指摘しておく。
残りのベンチマークは[7]による。
uf*およびuuf*ベンチマークは、相転移境界のランダムな3SATインスタンスであり、大量の探索を伴う可能性の高い問題での振る舞いを説明するために含まれている。
残りの問題は、構造化された問題での動作を説明するために選ばれた。

```
benchmark      vars clauses satisfiable time (ms) mini (ms) assigns
chat_80_1.cnf    13      31        true         0         1       9
chat_80_2.cnf    12      30        true         0         1       5
chat_80_3.cnf     8      14        true         0         1       7
chat_80_4.cnf     7      16        true         0         1       3
chat_80_5.cnf     7      16        true         0         1       4
chat_80_6.cnf     8      14        true         0         1       6
uf20-0903.cnf    20      91        true         0         1       8
uf50-0429.cnf    50     218        true        10         1      89
uf100-0658.cnf  100     430        true        20         1     176
uf150-046.cnf   150     645        true       290        15    3002
uf250-091.cnf   250    1065        true      2850       171   13920
uuf50-0168.cnf   50     218       false         0         1      79
uuf100-0592.cnf 100     430       false        50         6     535
uuf150-089.cnf  150     645       false       770        18    8394
uuf250-016.cnf  250    1065       false       t/o      1970
2bitcomp_5.cnf  125     310        true       130         1    7617
flat200-90.cnf  600    2237        true       380        12    1811
```

図3. SATソルバーの実験評価

このソルバーが発見されたコンテクストから生じた問題は、すべて素早く解かれ、変数代入をほとんど必要としないことがわかる。
解析[8]の1回の実行でソルバーへの呼び出しが何千回にもなる可能性があるこれらの問題では、大きなSATインスタンスを解く時間は時計の粒度以下であり、したがってソルバーは明らかに十分速い。
予想されるように、相転移問題では、探索量は問題の大きさとともに急激に増加する。
しかし、数百の節を持つインスタンスは依然として解かれ、この観察は構造化問題の結果によって確認される。
## 6 Concluding Discussion 結論

これまでのところ、PrologがSAT解法への簡単な入口を提供する方法を 強調してきた。
このセクションは、この実装技術の長所についての議論で締めくくる前に、取られたアプローチの限界を強調することから始めます。

SAT解法の挑戦は、問題の大きさとともに大きくなります。
これは、SATインスタンスの保存と探索空間の増大という2つの形で現れる。
プログラマは、何十万もの節を保存し、アクセスするために必要なきめ細かなメモリ制御を持っていません。
第2の問題に対処するためには、第4節で概説したような探索ヒューリスティックが必要である。
よく使われるヒューリスティックの1つは、解を含まない探索空間の領域を表す節を問題に追加する学習である[13]。
残念ながら、このPrologソルバーでは、学習された句への呼び出しがバックトラックで失われるため、これをきれいに達成する方法は明確でない。
一つのアプローチは、学習した節を黒板に保存し、バックトラックの適切な時点で問題に追加することであるが、このアプローチは制限的であり、魅力的でない（いくつかのソルバーで使用されているランダムな再スタートには適しているが）。
最後に注意すべき点は、ウォッチされるリテラルの実装にある。ウォッチされるリテラルは探索中に変更され、伝播中の変更はバックトラック時に元に戻される。
これにより、節のメンテナンスが容易になりますが、ウォッチされるリテラルが潜在的に持っている利点が失われます。
つまり、バックトラック時にウォッチされるリテラルを変更する必要がない[6]。

上記の欠点のため、本稿で紹介するソルバーは、国際的なSATコンペティション[12]の課題として設定された大規模で困難な問題で競争力を発揮することはできない。
しかし、このソルバーは、簡潔で自己完結的な方法で、ウォッチド・リテラルを用いたSAT解法の宣言的な記述を提供するものであり、多くの方法で拡張可能なものである。
さらに、Posベースのプログラム解析[8]におけるフィックスポイント計算の安定性の検出など、小中規模の問題には十分に役立つ性能を発揮する。
この文脈では、Prolog自体でコード化されたSATエンジンは、外国語インタフェー ス（[2]は、このインタフェースをユーザから隠していることに注意） を使わず、配布の問題を単純化し、SATインスタンスのProlog表現を外部の SATソルバーが使う内部C表現に変換するオーバヘッドを避けるので、魅力的である。

最後に、ソルバーはwww.soi.city.ac.uk/∼jacob/solver/で利用可能である。

## Acknowledgements 謝辞

本研究は、EPSRCの資金提供によるプロジェクトEP/E033105/1およびEP/E034519/1の支援を受けた。
著者らは、英国王立協会とセント・アンドリュース大学の寛大な支援に感謝したい。
また、有益なコメントをいただいた匿名の査読者にも感謝したい。
## References 参考文献

1. M. Bruynooghe. Enhancing a Search Algorithm to Perform Intelligent Backtracking. Theory and Practice of Logic Programming, 4(3):371–380, 2004.
2. M. Codish, V. Lagoon, and P. J. Stuckey. Logic Programming with Satisfiability. Theory and Practice of Logic Programming, 8(1):121–128, 2008.
3. M. Davis, G. Logemann, and D. Loveland. A Machine Program for Theorem Proving. Communications of the ACM, 5(7):394–397, 1962.
4. N. E´en and A. Biere. Effective Preprocessing in SAT through Variable and Clause Elimination. In International Conference on Theory and Applications of Satisfiability Testing, volume 3569 of Lecture Notes in Computer Science, pages 61–75, 2005.
5. N. E´en and N. S¨orensson. An Extensible SAT-solver. In Theory and Applications of Satisfiability Testing, volume 2919 of Lecture Notes in Computer Science, pages 502–518. Springer, 2003.
6. I. P. Gent, C. Jefferson, and I. Miguel. Watched Literals for Constraint Propagation in Minion. In Constraint Programming, volume 4204 of Lecture Notes in Computer Science, pages 182–197. Springer, 2006.
7. H. H. Hoos and T. St¨utzle. SATLIB: An Online Resource for Research on SAT. In SAT 2000, pages 283–292. IOS Press, 2000. http://www.satlib.org.
8. J. M. Howe and A. King. Positive Boolean Functions as Multiheaded Clauses. In International Conference on Logic Programming, volume 2237 of Lecture Notes in Computer Science, pages 120–134. Springer, 2001.
9. J. M. Howe and A. King. Efficient Groundness Analysis in Prolog. Theory and Practice of Logic Programming, 3(1):95–124, 2003.
10. A. King and J. C. Martin. Control Generation by Program Transformation. Fundamenta Informaticae, 69(1-2):179–218, 2006.
11. R. A. Kowalski. Algorithm = Logic + Control. Communication of the ACM, 22(7):424–436, 1979.
12. D. Le Berre, O. Roussel, and L. Simon. The International SAT Competitions Webpage, 2009. http://www.satcompetition.org/.
13. J. P. Marques-Silva and K. A. Sakallah. GRASP – a New Search Algorithm for Satisfiability. In International Conference on Computer-Aided Design, pages 220–227. ACM and IEEE Computer Society, 1996.
14. M. W. Moskewicz, C. F. Madigan, Y. Zhao, L. Zhang, and S. Malik. Chaff: Engineering an Efficient SAT Solver. In Design Automation Conference, pages 530–535. ACM Press, 2001.
15. L. Naish. Negation and Control in Logic Programs. Springer-Verlag, 1986.
16. L. Zhang and S. Malik. The Quest for Efficient Boolean Satisfiability Solvers. In Computer Aided Verification, volume 2404 of Lecture Notes in Computer Science, pages 17–36. Springer, 2002.
