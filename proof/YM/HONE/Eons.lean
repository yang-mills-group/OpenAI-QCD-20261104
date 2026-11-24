import YM.HONE.Mills
import YM.Talis.Nectar
import YM.Intag.Tess
/-!
  # EP rooted norm primitive output program.
  Accepts single-tile orbit prototypes, B grid. no even para label. Θ charge absorbed local.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox
open scoped BigOperators Classical
namespace CardsT
open Pilgrim Tess Column QCD.Plum UV QCD.Lat
open Finset MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills
variable {S:Scheme}{R:Side}{k i ℓ p n:ℕ}(A:Massive.Run S n R 6)
local notation "Z"=> S.side R
local notation "J"=> Site (S.side R p)
variable (z:Site (S.side R ℓ))(hj:p ≤ ℓ)(hp:Even R.val)(P:Site (S.side R p))(x:Cover)
set_option quotPrecheck false
local notation "X"=> (viewW S R hj)
local notation "T"=> mural X (evenW S R hp p) z
local notation "bT"=> Pilgrim.bout T P rfl x
-- Use as I.E.Spectral. units width this prototype
variable (U:Averaging)(Yq: Site (S.side R p) → Cover → Insertion (S.side R n) 6)(Wq:Site (S.side R p) → Cover → Insertion (S.side R i) 6)
local notation "Φ" i:arg=> Hole (Site (S.side R p)) S ℓ i
local notation "Ψ"=> doubleT A bT (fun _=>U) Yq Wq (i:=ℓ)
noncomputable abbrev sectorR (L:Averaging)(Y: Site (S.side R p) → Cover → Insertion (S.side R n) 6)(W: Site (S.side R p) → Cover → Insertion (S.side R i) 6)(u:Site (S.side R p)): Stud (S.side R n) 6:=checkE A ℓ L (Y u) (W u) (Pilgrim.bout T P rfl x u)
local notation "YY"=> sectorR A z hj hp P x U Yq Wq
variable (hi:ℓ≤ i) (hc:i ≤ n)
-- Ancestry sky extends from every i >=ℓ at same shift.
include hi hc
local notation "TJ"=> sky S R p n (hj.trans (hi.trans hc)) (evenW S R hp p) z
variable (u:Site (S.side R p))
-- premises consume: for each j transform with adj etc. use ℓ Cut transported.All >.; can supply C for every step (construct Below using homo Child t.j<h > but p≤ j? earlier smaller unknown S.r even if R even, holds.R, enough for T.Cose.Factory).
local notation "tit" j:arg => T.bandCut (post T P j).1 (post T P j).2
local notation "Yt" j:arg=> (TJ).bandCut (post T P j).1 (post T P j).2
variable (Cc:∀ i:ℕ, Site (S.side R p)→Cells.Cut (S.side R i)) -- helper
variable (hC:∀ j,ℓ ≤ j→ j < n→∀ t,Cc (j+1) t=gateH (Cc j t) (QCD.Flume.sliceL (S.step j) (S.sides_next R j)))
variable (ht: ∀ t:Site (S.side R p),Cc ℓ t=(mural (viewW S R hj) (evenW S R hp p) z).bandCut (post (mural (viewW S R hj) (evenW S R hp p) z) P t).1 (post (mural (viewW S R hj) (evenW S R hp p) z) P t).2)
local notation "Ω"=> μ T P
open Cylinder Massive.Patria
include ht hC
lemma heirs (j:ℕ)(he:ℓ ≤ j)(hs:j≤ n)(t:Site (S.side R p)) : Cc j t=(sky S R p j (hj.trans he) (evenW S R hp p) z).bandCut (post T P t).1 (post T P t).2:=by
     induction he with| refl=>unfold Column.sky; rw [homes S R]; exact ht t| @step j he ih=>rw [halos S R z (evenW S R hp p) (post T P t).1 hj he (post (mural (viewW S R hj) (evenW S R hp p) z) P t).2,hC j he hs,ih (le_trans (Nat.le_succ _) hs)] -- arity halos (a implicit?)
-- title transform.A Θ axis sign.
lemma rentsV (hx:u≠P)
    (hΦ:∀ (p:Cover), Cylinder.Action.adj (Cc ℓ u|>.pos) ⇑(Yq (Ω u) p)=⇑(Yq u ((Cc ℓ u|>.flip).act p))) (hW:∀ a b:Cover,Massive.Patria.march b (Yq u a)= Yq u (a+b))
    (hΦ1:∀ (p:Cover), Cylinder.Action.adj (Cc ℓ u|>.pos) ⇑(Wq (Ω u) p)=⇑(Wq u ((Cc ℓ u|>.flip).act p))) (hW1:∀ a b:Cover,Massive.Patria.march b (Wq u a)= Wq u (a+b)) : YY u=tallH (Yt u) (YY (Ω u)):=by
      let g:= fun j=> Cc j u; let b:= Pilgrim.passport T P rfl (u:=u); have hv:CompleteP (g ℓ) b:=by unfold g; rw[ht u]; exact paced (mural (viewW S R hj) (evenW S R hp p) z) P rfl u
      let a:= bT (Ω u); have hw:= CardsT.rentM A hc g (fun j hp h'=> hC j hp h' u) U a b hv (Yq (Ω u)) _ hΦ hW (Wq (Ω u)) _ hΦ1 hW1 hi; rw [← heirs z hj hp P hi hc Cc hC ht n (hi.trans hc) le_rfl u]; refine Eq.trans ?_ hw.symm; change checkE A ℓ U (Yq u) (Wq u) (bT u)=_; apply congr_arg; change bT u = b+ _; conv_lhs=> rw (transparency:=.default) [bout,dif_neg hx]
      rw (transparency:=.default) [add_comm b]; unfold g; rw [ht] -- heirs sig likely no A.P.Ax
-- pick serialization for output.L.Col.Touch.
omit hC ht
include hi hc
lemma orderedQ (hEnd:Potion (YY P))(hf:∀ u:Site (S.side R p),u≠P→ YY u=tallH (Yt u) (YY (Ω u))):∃ (m:ℕ)(t:Fin m→ Hole (Site (S.side R p)) S ℓ ℓ), Quills.crest t= Finset.univ ∧ Injective t ∧ ‖valueH A.regulator ((List.ofFn fun i=> Ψ (t i)).prod)‖=topH (TJ) A.regulator (YY P) P ^ Fintype.card (Site (S.side R p)):=by
     let I:= Site (S.side R p); let l:= (univ:Finset I).toList
     let f:I→Hole I S ℓ ℓ:=fun x=> ⟨x,0, Lattice.center_box _⟩; have hf0(x:Φ ℓ):x=f x.1 := (univSt S ℓ (I:=I):Set.InjOn _ _) (mem_univ _) (mem_univ _) rfl
     let t: Fin l.length→ Φ ℓ:=fun i=>f (l.get i); have hZ:List.ofFn t=l.map f:=by change List.ofFn (f∘l.get)=_; rw[←List.map_ofFn,List.ofFn_get]
     have hi': Injective t:= List.nodup_ofFn.mp (hZ.symm ▸ (List.Nodup.map (Function.LeftInverse.injective (g:=Prod.fst) (fun j:I=> (rfl : Prod.fst (f j)=_))) (Finset.nodup_toList _))) -- syntax
     refine ⟨l.length,t,?_ ,hi', ?_⟩
     · apply eq_univ_of_forall; intro x; have ht:x∈l.map f:=List.mem_map.mpr ⟨x.1,Finset.mem_toList.mpr (mem_univ _),hf0 x|>.symm⟩; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (hZ.symm ▸ ht); exact (exists_fix ..).2 ⟨i,rfl⟩
     rw [show (List.ofFn (fun i:Fin l.length=> Ψ (t i)))= l.map YY from ?_]; swap; · change List.ofFn (Ψ∘t)=_; rw (transparency:=.default) [←List.map_ofFn,hZ,List.map_map]; congr 1; exact funext (fun i=> docket ..)
     have ht(b:I):Chess.SignedEq (palmH (TJ) (YY P) P b) (YY b):= Pilgrim.income _ _ _ _ _ _ YY hf hEnd b; exact Eq.symm ((top_power (TJ) A.regulator P (YY P)).trans (Lyre.signsV A.regulator (Lyre.apportion (TJ) (YY P) P YY ht)))
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.rentsV
#print axioms YM.Intag.CardsT.orderedQ
