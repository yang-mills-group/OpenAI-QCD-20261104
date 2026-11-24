import YM.HONE.Eons
import YM.HONE.Greet
/-! # Replica masks through Run. Geometry & earns. No assumption on convergence. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter MeasureTheory RG
open Lattice Wilson Cells YM.Next.Rank.Station
open Massive Massive.Lyre Massive.Patria.Hub Massive.Patria.Depth Massive.Romance QCD QCD.Tide Push.GridApprox QCD.Lat QCD.Grass MassiveQCD MassiveQCD.Cupola
open scoped BigOperators Classical
namespace CardsT
open Pilgrim Tess Column Finset Plum
variable {S:Scheme}{R:Side}{k i ℓ p n:ℕ}(A:Massive.Run S n R 6)
variable (z:Site (S.side R ℓ))(hj:p ≤ ℓ)(hp:Even R.val)(P:Site (S.side R p))(x:Cover)
local notation "Pr"=> Site (S.side R p)
local notation "Ŧ"=> evenW S R hp p
local notation "T"=>mural (viewW S R hj) (evenW S R hp p) z
local notation "X"=> Pilgrim.bout T P rfl x
local notation "μT"=> μ T P
local notation "Q" k:arg=> Hole (Site (S.side R p)) S ℓ k
local notation "Pv" u:arg=> (post T P u)
set_option quotPrecheck false
local notation "κ" t:arg=> (mural (viewW S R hj) (evenW S R hp p) z).bandCut (post (mural (viewW S R hj) (evenW S R hp p) z) P t).1 (post (mural (viewW S R hj) (evenW S R hp p) z) P t).2
lemma juried {j:ℕ}:∃ C:∀ i:ℕ, Site (S.side R p)→Cells.Cut (S.side R i), (∀ i:ℕ,ℓ≤ i→ i<j→∀ t,C (i+1) t=gateH (C i t) (QCD.Flume.sliceL (S.step i) (S.sides_next R i)))∧∀ t,C ℓ t=κ t:=by
     let f (k:ℕ) (t:Site (S.side R p)): Cells.Cut (S.side R k):= if h:ℓ≤ k then (Column.sky S R p k (hj.trans h) (evenW S R hp p) z).bandCut (Pv t).1 (Pv t).2 else (mural (viewW S R (le_refl k)) (evenW S R hp k) 0).bandCut (0:Site (S.side R k)) 0
     refine ⟨f,fun i h hv t=>?_,fun v=>?_⟩
     · unfold f; rw [dif_pos (Nat.le_succ_of_le h),dif_pos h]; exact Column.halos S R z (evenW S R hp p) (post T P t).1 hj h _
     unfold f; rw[dif_pos (le_refl ℓ)]; unfold Column.sky; rw[Column.homes S R]
variable (σ:Site (S.side R p)→Bool)(U:Averaging)(Yq: Site (S.side R p) → Cover → Insertion (S.side R n) 6)(Wq:Site (S.side R p) → Cover → Insertion (S.side R i) 6)(hi:ℓ ≤ i)(hn:i ≤ n)
open Massive.Patria Massive.Chess
local notation "T★"=> sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z
local notation "Ty" r:arg=> sectorR A z hj hp P x U Yq Wq r
variable (hW:∀ v a b, Massive.Patria.march b ⇑(Wq v a)=⇑(Wq v (a+b))) (hY:∀ v a b, Massive.Patria.march b ⇑(Yq v a)=⇑(Yq v (a+b)))
open MassiveQCD.Sample
-- honest Root norm. stamped on same z!`
include hi hn hW hY
lemma stellar (hx:∀ u:Pr,∀ x V, Hom (σ u) (Yq u x V))(hy:∀ u:Pr,∀ x V, Hom (σ u) (Wq u x V))
    (hY0:∀ t:Pr,t ≠ P→∀ b:Cover,Cylinder.Action.adj (κ t).pos (Yq (μT t) b)= Yq t ((κ t).flip.act b))(hW0:∀ t:Pr,t ≠ P→∀ b:Cover,Cylinder.Action.adj (κ t).pos (Wq (μT t) b)= Wq t ((κ t).flip.act b)):∃ (m:ℕ)(f:Fin m→Hole (Site (S.side R p)) S ℓ ℓ),Quills.crest f=Finset.univ ∧ Injective f ∧ ‖valueH A.regulator ((List.ofFn (fun i'=> doubleT A X (fun _=>U) Yq Wq (f i'))).prod)‖=topH (sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z) A.regulator (checkE A ℓ U (Yq P) (Wq P) x) P ^ Fintype.card (Site (S.side R p)):=by
    obtain ⟨C,hC,hT⟩:=juried z hj hp P (j:=n)
    have ht(u:Pr)(h:u≠P): Ty u=tallH ((sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z).bandCut (Pv u).1 (Pv u).2) (Ty (μT u)):=by
         apply CardsT.rentsV A z hj hp P x U Yq Wq hi hn u C hC hT h ?_ (hY u) ?_ (hW u)
         all_goals rw[hT u]; first | exact hY0 u h| exact hW0 u h
    have hx':Ty P=checkE A ℓ U (Yq P) (Wq P) x:=by unfold sectorR; rw[show Pilgrim.bout T P rfl x P=x from Tess.spec T P _ _ _] <;> rfl
    rw [←hx']; apply orderedQ _ z hj hp P x U Yq Wq hi hn ?_ ht
    let v:Hole (Site (S.side R p)) S ℓ ℓ:=⟨P,0,Lattice.center_box _⟩; refine ⟨σ P, ?_⟩
    intro V; have hz:= coatingT A (I:=Pr) (Pilgrim.bout T P rfl x) Wq hi hn (fun _=>U) σ hy Yq hx v V -- arg order
    rw[CardsT.docket ..] at hz; exact hz
omit hi hn hY hW
variable (M:ℕ)
lemma costsF (hx:wrap _ x∈ (mural (viewW S R hj) (evenW S R hp p) z).margin P M) (u:Site (S.side R p)): wrap _ (X u) ∈ (T).margin u M := Tess.prices_f (mural (viewW S R hj) (evenW S R hp p) z) P (fun _:Unit=>x) rfl u () _ hx
lemma guardian (hx:wrap _ x∈ (mural (viewW S R hj) (evenW S R hp p) z).margin P M) :∀ u v:Pr,u≠v→2*M < separation (wrap (S.side R ℓ) (X u)) (wrap _ (X v)):=fun u v he=>by rw[two_mul]; exact crimp (viewW S R hj) z u (evenW S R hp p) (viewOdd ..) (costsF z hj hp P x M hx u) (costsF z hj hp P x M hx v) he
lemma loc (hx:wrap _ x∈ (mural (viewW S R hj) (evenW S R hp p) z).margin P M) :∀ v:(Q ℓ),wrap (S.side R ℓ) (showX S ℓ ℓ X v) ∈ (T).margin v.1 M:=fun v=>by
     have hu : showX S ℓ ℓ (X:Pr → Cover) v=X v.1:= CardsT.through ..; rw [hu]; exact costsF z hj hp P x M hx _
lemma sparksP (p:ℕ) : Fires (fun j: Hole (Site (S.side R p)) S ℓ ℓ=> j.1) 1 :=fun i=>card_le_one.mpr fun x hx y hy=>(show Set.InjOn _ _ from (univSt S ℓ (I:= Site (S.side R p)):Set.InjOn _ _)) (mem_univ _) (mem_univ _) (((mem_filter.mp hx).2).trans ((mem_filter.mp hy).2).symm)
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.stellar
#print axioms YM.Intag.CardsT.loc
#print axioms YM.Intag.CardsT.guardian
#print axioms YM.Intag.CardsT.sparksP
