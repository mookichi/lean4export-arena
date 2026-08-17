# .olean バイナリフォーマット (Lean 4 v4.30.0)

Phase 0 で実測（`Phase0Test.olean` をバイト単位でパース）し、C++ ソース
（`src/library/module.cpp`, `src/runtime/compact.cpp`, `src/runtime/object.h`,
`src/include/lean/lean.h` @ v4.30.0）と照合した結果。

## 重要な結論

**`.olean` は MessagePack 風のタグ付きフォーマットではない。**
Lean オブジェクトグラフのメモリレイアウトをそのまま書き出した
**compacted region** である。ポインタは 8 バイトの「オフセット」として
直列化され、`base_addr`（ヘッダ内）からの相対で解釈する。

## ファイル全体の構造

```
+--------------------------------------------------+
| olean_header (88 bytes, 下記参照)                  |
+--------------------------------------------------+
| compacted region (root offset 1つ + オブジェクト群) |
+--------------------------------------------------+
```

## ヘッダ (olean_header, 88 bytes, packed)

| offset | size | 内容 |
|--------|------|------|
| 0      | 5    | マジック `"olean"` |
| 5      | 1    | version = 2 (構造変更で増える) |
| 6      | 1    | flags: bit0 = GMP使用 (1) / Lean-native bignum (0) |
| 7      | 33   | Lean バージョン文字列 (`"4.30.0"` + NUL padding) |
| 40     | 40   | build githash (`d024af...622` + NUL padding) |
| 80     | 8    | base_addr (size_t, ファイル先頭の mmap 想定アドレス) |

実測 (`Phase0Test.olean`):
- marker = `b'olean'`, version = 2, flags = 0x1 (GMP)
- lean_version = `b'4.30.0'`
- githash = `b'd024af099ca4bf2c86f649261ebf59565dc8c622'`
- base_addr = `0x561661b60000`

`base_addr` はモジュール名のハッシュから決まる（`name(mod,true).hash() % 0x7f0000000000` を 64KB にアライン）。

## compacted region の読み方

ファイルオフセット 88 以降が compacted region。

### オフセットの解釈

領域内の「ポインタ」はすべて 8 バイトの整数で、
```
ファイル内オフセット = ポインタ値 - base_addr
```
で求める。root は領域先頭 (offset 88) の 8 バイト。

実測: root_offset = `0x561661bb3d00` → ファイル内 offset `0x53d00`。

### 値の種類 (8 バイト単位)

- **スカラー** (`v & 1 == 1`): 値 = `v >> 1`。boxed の小さい Nat / Bool / インデックス等。
  - `Name.anonymous` はスカラー `1` (box(0)) で表現される。
- **オブジェクト** (`v & 1 == 0`): `v` はオフセット。先頭 8 バイトが `lean_object` ヘッダ:

```
typedef struct {
    int      m_rc;       // 4 bytes  (compacted では 0)
    unsigned m_cs_sz:16; // 2 bytes  (compacted ではオブジェクトサイズ)
    unsigned m_other:8;  // 1 byte   (ctor ではオブジェクトフィールド数)
    unsigned m_tag:8;    // 1 byte
} lean_object;
```

### タグ (m_tag)

| 値 | 意味 |
|----|------|
| 0..243 | コンストラクタ (フィールド数 = m_other) |
| 244 | LeanPromise |
| 245 | LeanClosure (compacted 不可) |
| 246 | LeanArray (オブジェクトの配列) |
| 247 | LeanStructArray |
| 248 | LeanScalarArray |
| 249 | LeanString |
| 250 | LeanMPZ (big Nat / Int) |
| 251 | LeanThunk |
| 252 | LeanTask |
| 253 | LeanRef |
| 254 | LeanExternal (compacted 不可) |
| 255 | LeanReserved |

### オブジェクトのレイアウト

- **ctor** (tag ≤ 243): header(8) + オブジェクトフィールド m_other 個 (各 8B) [+ スカラーフィールド]
  - フィールド i のオフセット: `obj_off + 8 + 8*i`
  - スカラーフィールド (Bool 等) はオブジェクトフィールドの後に続く
  - **スカラーパッキング**: 複数のスカラーフィールドはフィールド順に 1 バイトずつ 8 バイトスロットに詰められる。
    例: RecursorVal の k, isUnsafe は 1 スロット (k=byte0, isUnsafe=byte1)。InductiveVal の isRec, isUnsafe, isReflexive も 1 スロット。
- **LeanArray** (246): header(8) + size(8) + capacity(8) + data[8*size]
  - 要素 j のオフセット: `arr_off + 24 + 8*j`
- **LeanString** (249): header(8) + byte_size(8, NUL 含む) + capacity(8) + utf8_len(8) + data[byte_size]
  - データは `off + 32` から byte_size バイト (末尾 NUL を含む)
- **LeanMPZ** (250): エンコーディングはヘッダの flags bit0 で選択 (GMP=1 / Lean-native=0)
  - **GMP**: header(8) + `__mpz_struct { _mp_alloc:int32(+8), _mp_size:int32(+12), _mp_d:ptr(+16) }` + リム列(+24)
    - compactor が `_mp_alloc = nlimbs` に設定し、リムを +24 にコピーする。`_mp_size` は符号付きリム数 (負 = 負数)。
  - **Lean-native**: header(8) + `{ m_sign:bool(+8), pad, m_size:u64(+16), m_digits:ptr(+24) }` + 桁列(+32)

## ModuleData (root オブジェクト)

root は `ModuleData` 構造体 (Lean の `structure ModuleData`, tag=0)。

フィールド (実測: obj_fields = 5、isModule はスカラー領域):

| obj field | 内容 | 型 |
|-----------|------|----|
| 0 | imports | Array Import |
| 1 | constNames | Array Name |
| 2 | constants | Array ConstantInfo |
| 3 | extraConstNames | Array Name |
| 4 | entries | Array (Name × Array EnvExtensionEntry) |

スカラー領域: isModule : Bool (実測では false=0)

実測値 (Phase0Test.olean): imports=3, constNames=117, constants=117,
extraConstNames=36, entries=29。

### Import 構造体

`structure Import where module : Name; importAll : Bool := false`
- obj field 0: module (Name)
- スカラー: importAll

### Name の表現

```lean
inductive Name where
  | anonymous | str (pre : Name) (s : String) | num (pre : Name) (n : Nat)
```
- anonymous: スカラー box(0)（オブジェクトでない）
- str: tag=1, 2 obj fields (pre: Name, s: String) + スカラー 1 スロット (ハッシュ。デコード不要)
- num: tag=2, 2 obj fields (pre: Name, n: Nat) + スカラー 1 スロット (ハッシュ) — n はスカラー or MPZ

## ConstantInfo のタグと各 val のレイアウト

`constants` 配列の各要素は `ConstantInfo` (inductive)。タグはコンストラクタ順
(`Lean/Declaration.lean` の `inductive ConstantInfo`): **axiom=0, defn=1, thm=2, opaque=3,
quot=4, induct=5, ctor=6, rec=7** (Phase 1 で実測確定)。

各 `ConstantInfo` は obj field 1 個 = 対応する `XxxVal`。`XxxVal` は常に tag=0 の ctor で、
先頭に `ConstantVal` サブオブジェクト (tag=0, obj 3 個: name / levelParams / type) を持つ
(`extends ConstantVal` の実行時ネスト)。

| CI tag | val の obj fields | スカラースロット |
|--------|-------------------|------------------|
| 0 axiom | [cv] | [isUnsafe] |
| 1 defn | [cv, value, hints, all] | [safety] |
| 2 thm | [cv, value, all] | — |
| 3 opaque | [cv, value, all] | [isUnsafe] |
| 4 quot | [cv] | [kind] |
| 5 induct | [cv, numParams, numIndices, all, ctors, numNested] | [isRec, isUnsafe, isReflexive] (1 スロットにパック) |
| 6 ctor | [cv, induct, cidx, numParams, numFields] | [isUnsafe] |
| 7 rec | [cv, all, numParams, numIndices, numMotives, numMinors, rules] | [k, isUnsafe] (1 スロットにパック) |

Nat フィールド (numParams 等) は boxed スカラー (`v<<1|1`) または MPZ オブジェクト。
`hints` はスカラー (0=opaque, 1=abbrev) または tag=2 オブジェクト (regular, 高さ UInt32 を生値で保持)。
`safety`/`kind` は生バイト (unsafe=0/safe=1/partial=2, type=0/ctor=1/lift=2/ind=3)。

### Expr のレイアウト (タグ 0..11)

| tag | コンストラクタ | obj fields | スカラー |
|-----|----------------|------------|----------|
| 0 | bvar | [idx] | — |
| 1 | fvar | [name] | — (.olean には現れない) |
| 2 | mvar | [name] | — (.olean には現れない) |
| 3 | sort | [level] | — |
| 4 | const | [name, levels] | — |
| 5 | app | [fn, arg] | — |
| 6 | lam | [name, type, body] | data word + binderInfo byte (スロット1の byte0) |
| 7 | forallE | [name, type, body] | data word + binderInfo byte |
| 8 | letE | [name, type, value, body] | data word + nondep byte |
| 9 | lit | [Literal] | data word |
| 10 | mdata | [entries list, expr] | — |
| 11 | proj | [name, idx, struct] | — |

data word = `hash | depth<<32 | flags<<40 | bvarRange<<44` (ランタイム用、デコード不要)。
Literal: tag 0 = natVal [Nat], tag 1 = strVal [String] (小さな natVal はスロットに直接 boxed で入ることもある)。
binderInfo byte: default=0, implicit=1, strictImplicit=2, instImplicit=3。

### MData / KVMap (mdata のペイロード)

**v4.30.0 では `KVMap` は PHashMap ではなく `List (Name × DataValue)`**
(`Lean/Data/KVMap.lean`: `structure KVMap where entries : List (Name × DataValue)`)。
単一フィールド構造体はコード生成で展開され、mdata の obj field 0 に **entries の List が直接**入る:

```
mdata: tag=10, [entries(List), expr]
List.cons: tag=1, [head, tail] / nil: スカラー box(0)
pair: tag=0, [fst(Name), snd(DataValue)]
DataValue: ofString=0 [String] / ofBool=1 [Bool スカラー] / ofName=2 [Name]
           ofNat=3 [Nat] / ofInt=4 [Int] / ofSyntax=5 [Syntax]
Int: ofNat=0 [Nat] / negSucc=1 [Nat]
```

エクスポータの `KVMap.toJson` は `{ "<Name.toString(unescaped)>": "<reprStr DataValue>" }`
(キーは JSON オブジェクトなので辞書順にソート)。reprStr の形式:
`Lean.DataValue.ofBool true` / `Lean.DataValue.ofString "..."` /
`Lean.DataValue.ofName \`foo.bar` (特殊文字は «» エスケープ) /
`Lean.DataValue.ofName (Lean.Name.mkNum \`foo 42)` (maxPrec では常に括弧) /
`Lean.DataValue.ofNat 42` / `Lean.DataValue.ofInt (-5)` (負数のみ括弧)。

### Level のレイアウト (タグ 0..5)

zero=スカラー box(0), succ=[level], max=[a,b], imax=[a,b], param=[name], mvar=[name]。

## デコード検証

### Phase 0: Python 手書きデコード

結果が Lean の `readModuleData` の出力と完全に一致することを確認済み:

```
Lean:   import Init importAll=false / import Init importAll=false / import Lean importAll=false
Python: import[0]: module='Init' / import[1]: module='Init' / import[2]: module='Lean'
```

### Phase 1: Rust デコーダ (`rust/crates/olean`)

ツールチェーン Init/*.olean (47 個) と `.lake` の全 olean (51 個) について、
`readModuleData` の集計 (imports / constNames / constants / extraConstNames / entries) と
**全数一致**。さらに:

- `Init/Core.olean` の constNames 1124 個が**名前・順序とも** Lean と一致
- ConstantInfo 種別分布 (axiom=473, defn=475, thm=8, opaque=0, quot=0, induct=52, ctor=64, rec=52) が一致
- `Eq.rec` の `k=true, isUnsafe=false` (スカラーパッキングの検証)
- `withBigNat` の `natVal 100000000000000023456789` (MPZ デコード) が golden と一致
- `deepAxiom` (バインダ 1500 段ネスト) のデコード成功
- リリースビルドで `Init/Core.olean` (1.6MB) の全オブジェクトウォークが ~7ms

## Rust 実装への示唆

- BinaryReader は不要。代わりに「オフセット解決 + オブジェクトウォーカー」を実装する。
- 8 バイト値が奇数か偶数かでスカラー/ポインタを判定。
- サイズはすべて 64-bit little-endian。
- すべてのオフセットは `base_addr` から引いてファイル位置を得る。
- root ポインタは**ファイルオフセット 88** (ペイロード先頭) にある。
- 循環参照はない（compacted region は DAG）。
- オブジェクトは共有 (DAG) なので、デコードはオフセット単位でメモ化する。
