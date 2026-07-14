theory Problema_6_Provas
  imports Main
begin

(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO cat
  ============================================================
*)

fun cat :: "'a list ⇒ 'a list ⇒ 'a list" where
  "cat [] l = l"
| "cat (h # t) l = h # cat t l"


(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO tamanho
  ============================================================
*)

fun tamanho :: "'a list ⇒ nat" where
  "tamanho [] = 0"
| "tamanho (h # t) = 1 + tamanho t"


(*
  ============================================================
  DEFINIÇÃO DO TIPO arvbin
  ============================================================
*)

datatype 'a arvbin =
    Vazia
  | No "'a arvbin" 'a "'a arvbin"


(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO numnodos
  ============================================================
*)

fun numnodos :: "'a arvbin ⇒ nat" where
  "numnodos Vazia = 0"
| "numnodos (No L x R) =
      1 + numnodos L + numnodos R"


(*
  ============================================================
  DEFINIÇÃO DA FUNÇÃO conteudo
  ============================================================
*)

fun conteudo :: "'a arvbin ⇒ 'a list" where
  "conteudo Vazia = []"
| "conteudo (No L x R) =
      x # cat (conteudo L) (conteudo R)"


(*
  ============================================================
  PROVA 1
  ============================================================

  tamanho(cat(L1,L2))
  =
  tamanho(L1)+tamanho(L2)
*)

theorem tamanho_cat :
  "tamanho (cat l1 l2) =
   tamanho l1 + tamanho l2"

proof (induction l1)

  case Nil

  have "tamanho (cat [] l2)
        = tamanho l2"
    by simp

  also have "... =
        0 + tamanho l2"
    by simp

  also have "... =
        tamanho [] + tamanho l2"
    by simp

  finally show ?case .

next

  case (Cons h t)

  have "tamanho (cat (h # t) l2)
        = tamanho (h # cat t l2)"
    by simp

  also have "... =
        1 + tamanho (cat t l2)"
    by simp

  also have "... =
        1 + (tamanho t + tamanho l2)"
    using Cons.IH by simp

  also have "... =
        (1 + tamanho t) + tamanho l2"
    by simp

  also have "... =
        tamanho (h # t) + tamanho l2"
    by simp

  finally show ?case .

qed


(*
  ============================================================
  PROVA 2
  ============================================================

  numnodos(A)
  =
  tamanho(conteudo(A))
*)

theorem numnodos_conteudo :
  "numnodos A =
   tamanho (conteudo A)"

proof (induction A)

  (*
    ========================================================
    CASO BASE
    ========================================================

    A = Vazia
  *)

  case Vazia

  have "numnodos Vazia
        = tamanho (conteudo Vazia)"
    by simp

  then show ?case .

next

  (*
    ========================================================
    PASSO INDUTIVO
    ========================================================

    Hipóteses de indução:

      numnodos L = tamanho(conteudo L)

      numnodos R = tamanho(conteudo R)

    Devemos provar:

      numnodos(No L x R)
      =
      tamanho(conteudo(No L x R))
  *)

  case (No L x R)

  have "numnodos (No L x R)
        = 1 + numnodos L + numnodos R"
    by simp

  also have "... =
        1 + tamanho (conteudo L)
          + tamanho (conteudo R)"
    using No.IH by simp

  also have "... =
        1 + tamanho
              (cat (conteudo L)
                   (conteudo R))"
    using tamanho_cat by simp

  also have "... =
        tamanho
          (x # cat (conteudo L)
                     (conteudo R))"
    by simp

  also have "... =
        tamanho
          (conteudo (No L x R))"
    by simp

  finally show ?case .

qed

end