theory Problema_1_Cat
  imports Main
begin

(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO cat
  ============================================================

  A função cat concatena duas listas.

  Tipo:
    'a list \<Rightarrow> 'a list \<Rightarrow> 'a list

  Significa:
    recebe duas listas de qualquer tipo ('a)
    e retorna uma nova lista.
*)

fun cat :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where

  (*
    Caso base da concatenação.

    Se a primeira lista é vazia [],
    então o resultado é simplesmente a segunda lista.
  *)
  "cat [] l = l"

| (*
     Caso recursivo.

     h = cabeça da lista
     t = cauda da lista

     A concatenação preserva o primeiro elemento
     e concatena o restante da lista recursivamente.
   *)
  "cat (h#t) l = h # cat t l"


(*
  DEFINIÇÃO DA FUNÇÃO tamanho

  A função tamanho conta quantos elementos
  existem em uma lista.
*)

fun tamanho :: "'a list \<Rightarrow> nat" where

  (*
    Caso base:
    lista vazia possui tamanho 0.
  *)
  "tamanho [] = 0"

| (*
     Caso recursivo:

     Uma lista h#t possui:
       1 elemento (h)
       +
       tamanho do restante da lista (t)
   *)
  "tamanho (h#t) = 1 + tamanho t"


(*
  ============================================================
  TEOREMA PRINCIPAL
  ============================================================

  Queremos provar que:

    tamanho(cat l1 l2)
      =
    tamanho l1 + tamanho l2

  Ou seja:

    O tamanho da concatenação
    é igual à soma dos tamanhos.
*)

theorem tamanho_cat :
  "tamanho (cat l1 l2) = tamanho l1 + tamanho l2"

proof (induction l1)

  (*
    ========================================================
    CASO BASE
    ========================================================

    Aqui l1 = []
  *)

  case Nil

  (*
    Expandindo cat [] l2.

    Pela definição de cat:
      cat [] l2 = l2
  *)
  have "tamanho (cat [] l2) = tamanho l2"
    by simp

  (*
    Reescrevendo tamanho l2 como:
      0 + tamanho l2
  *)
  also have "... = 0 + tamanho l2"
    by simp

  (*
    Pela definição:
      tamanho [] = 0

    Então:
      0 + tamanho l2
      =
      tamanho [] + tamanho l2
  *)
  also have "... = tamanho [] + tamanho l2"
    by simp

  (*
    Conclusão do caso base.
  *)
  finally show ?case .


next

  (*
    ========================================================
    PASSO INDUTIVO
    ========================================================

    Assumimos que a propriedade vale para t
    e provamos para (h # t)
  *)

  case (Cons h t)

  (*
    Hipótese de indução disponível:

      tamanho (cat t l2)
        =
      tamanho t + tamanho l2
  *)

  (*
    Expandindo a definição de cat.
  *)
  have "tamanho (cat (h # t) l2)
      = tamanho (h # cat t l2)"
    by simp

  (*
    Expandindo a definição de tamanho.
  *)
  also have "... = 1 + tamanho (cat t l2)"
    by simp

  (*
    Aplicando a hipótese de indução.
  *)
  also have "... = 1 + (tamanho t + tamanho l2)"
    using Cons.IH by simp

  (*
    Reorganizando a soma.

    Isabelle usa associatividade da soma.
  *)
  also have "... = (1 + tamanho t) + tamanho l2"
    by simp

  (*
    Reescrevendo:
      1 + tamanho t

    como:
      tamanho (h # t)
  *)
  also have "... = tamanho (h # t) + tamanho l2"
    by simp

  (*
    Conclusão do passo indutivo.
  *)
  finally show ?case .

qed


(* CASOS DE TESTE*)

(* Teste 1: concatenação de listas vazias*)
value "cat ([]::nat list) []"
(* Resultado esperado:[] *)

(*Teste 2: concatenação simples*)
value "cat [1::nat,2] [3,4]"
(* Resultado esperado:[1,2,3,4] *)

(* Teste 3: tamanho de lista vazia *)
value "tamanho ([]::nat list)"
(* Resultado esperado: 0 *)

(* Teste 4: tamanho de lista com elementos *)
value "tamanho [10::nat,20,30]"
(* Resultado esperado:  3 *)

(* Teste 5: tamanho após concatenação *)
value "tamanho (cat [1::nat,2] [3,4,5])"
(* Resultado esperado: 5 *)

(* Teste 6: verificação direta do teorema *)
value "tamanho (cat [1::nat,2] ([3,4]::nat list))"
value "tamanho ([1,2]::nat list) + tamanho ([3,4]::nat list)"
(* Ambos devem resultar em: 4 *)

end