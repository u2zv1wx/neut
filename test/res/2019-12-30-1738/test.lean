-- leanで同様のプログラムを書いてみる。
definition zero : ℕ :=
  (λ (itself : Type -> Type),
    (λ id,
      (λ (asc : (Π (A : Type) (x : A), itself A)),
        0) id)
    (λ (A : Type) (x : A), x))
  (λ (x : Type), x) -- 「直接」適用されているから、実際にはitselfの定義を保持することができる

-- Leanでも同様にuntypedになった。エラーメッセージを明記しておく：
--   type mismatch at application
--     (λ (id : Π (A : Type), A → itself A), (λ (asc : Π (A : Type), A → itself A), 0) id) (λ (A : Type) (x : A), x)
--   term
--     λ (A : Type) (x : A), x
--   has type
--     Π (A : Type), A → A
--   but is expected to have type
--     Π (A : Type), A → itself A
-- そうだよね、こうなるよね。
-- 実際、itselfに対応するlambdaを適当な変数に束縛すると、それは適用されるものによってidの型を変えるものになるだろう。
-- だから、言われてみれば、こっちのほうが正しいということがわかる。
-- こうして考えてみると、じつはletがあるほうがいいのでは、という気がしてくるわけだ。
