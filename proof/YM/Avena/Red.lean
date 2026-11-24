import YM.HONE.Hearth
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
-- title transform.A Θ axis sign.
local notation "YA" s:arg=> ⇑(checkedT U (ratioTo S n ℓ) (Yq s) (bT s))
lemma rentsG (hx:u≠P)
    (hΦ:∀ (p:Cover), Cylinder.Action.adj (Cc ℓ u|>.pos) ⇑(Yq (Ω u) p)=⇑(Yq u ((Cc ℓ u|>.flip).act p))) (hW:∀ a b:Cover,Massive.Patria.march b (Yq u a)= Yq u (a+b))
 : YA u=tallH (Yt u) (YA (Ω u)):=by
      let g:= fun j=> Cc j u; let b:= Pilgrim.passport T P rfl (u:=u); have hv:CompleteP (g ℓ) b:=by unfold g; rw[ht u]; exact paced (mural (viewW S R hj) (evenW S R hp p) z) P rfl u
      let a:= bT (Ω u); have hw:= CardsT.criesT g (fun j hp h'=> hC j hp h' u) U a b hv (Yq (Ω u)) _ hΦ hW (hi.trans hc); rw [← heirs z hj hp P hi hc Cc hC ht n (hi.trans hc) le_rfl u]; refine Eq.trans ?_ hw.symm; change ⇑(checkedT U (ratioTo S n ℓ) (Yq u) (bT u))=_; apply congr_arg; apply congr_arg; change bT u = b+ _; conv_lhs=> rw (transparency:=.default) [bout,dif_neg hx]
      rw (transparency:=.default) [add_comm b]; unfold g; rw [ht] -- heirs sig likely no A.P.Ax
-- pick serialization for output.L.Col.Touch.
omit hC ht
include hi hc
lemma orderedR (hEnd:Potion (YA P))(hf:∀ u:Site (S.side R p),u≠P→ YA u=tallH (Yt u) (YA (Ω u))):∃ (m:ℕ)(t:Fin m→ Hole (Site (S.side R p)) S ℓ ℓ), Quills.crest t= Finset.univ ∧ Injective t ∧ m = Fintype.card (Site (S.side R p)) ∧ ‖A.regulator.average (CardsT.rolledT bT (fun _=>U) Yq m t)‖=topH (TJ) A.regulator (YA P) P ^ Fintype.card (Site (S.side R p)):=by
     let I:= Site (S.side R p); let l:= (univ:Finset I).toList
     let f:I→Hole I S ℓ ℓ:=fun x=> ⟨x,0, Lattice.center_box _⟩; have hf0(x:Φ ℓ):x=f x.1 := (univSt S ℓ (I:=I):Set.InjOn _ _) (mem_univ _) (mem_univ _) rfl
     let t: Fin l.length→ Φ ℓ:=fun i=>f (l.get i); have hZ:List.ofFn t=l.map f:=by change List.ofFn (f∘l.get)=_; rw[←List.map_ofFn,List.ofFn_get]
     have hi': Injective t:= List.nodup_ofFn.mp (hZ.symm ▸ (List.Nodup.map (Function.LeftInverse.injective (g:=Prod.fst) (fun j:I=> (rfl : Prod.fst (f j)=_))) (Finset.nodup_toList _))) -- syntax
     refine ⟨l.length,t,?_ ,hi', by simp[l,I], ?_⟩
     · apply eq_univ_of_forall; intro x; have ht:x∈l.map f:=List.mem_map.mpr ⟨x.1,Finset.mem_toList.mpr (mem_univ _),hf0 x|>.symm⟩; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp (hZ.symm ▸ ht); exact (exists_fix ..).2 ⟨i,rfl⟩
     change ‖valueH A.regulator ⇑(CardsT.rolledT bT (fun _=>U) Yq l.length t)‖ = _; rw [show ⇑(CardsT.rolledT bT (fun _=>U) Yq l.length t)= (l.map (fun i=> YA i)).prod from ?_]; swap; · let w:=earnL S ℓ n ℓ bT (fun _=>U) Yq; let L:Insertion (S.side R n) 6→* Stud (S.side R n) 6:={toFun:=fun V=>V,map_mul':=fun _ _=>rfl,map_one':=rfl}; let h:=map_list_prod L (List.ofFn (w∘t)); refine h.trans ?_; rw (transparency:=.default) [← List.map_ofFn,hZ,List.map_map,List.map_map]; congr 1; refine congr_arg (fun F=>List.map F l) ?_; funext i; change ⇑(earnL S ℓ n ℓ bT (fun _=>U) Yq (f i))= _; rw[firstE]; rfl
     have ht(b:I):Chess.SignedEq (palmH (TJ) (YA P) P b) (YA b):= Pilgrim.income _ _ _ _ _ _ (fun i=>YA i) hf hEnd b; exact Eq.symm ((top_power (TJ) A.regulator P (YA P)).trans (Lyre.signsV A.regulator (Lyre.apportion (TJ) (YA P) P (fun i=>YA i) ht)))
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.rentsG
#print axioms YM.Intag.CardsT.orderedR
