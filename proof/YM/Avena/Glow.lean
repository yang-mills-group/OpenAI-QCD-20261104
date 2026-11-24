import YM.Avena.Red
import YM.Intag.Glyphs
import YM.Pods.Cove
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
variable (σ:Site (S.side R p)→Bool)(U:Averaging)(Yq: Site (S.side R p) → Cover → Insertion (S.side R n) 6)(Wq:Site (S.side R p) → Cover → Insertion (S.side R i) 6)(hi:ℓ ≤ i)(hn:i ≤ n)
open Massive.Patria Massive.Chess
local notation "T★"=> sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z
local notation "Ty" r:arg=> sectorR A z hj hp P x U Yq Wq r
variable (hW:∀ v a b, Massive.Patria.march b ⇑(Wq v a)=⇑(Wq v (a+b))) (hY:∀ v a b, Massive.Patria.march b ⇑(Yq v a)=⇑(Yq v (a+b)))
open MassiveQCD.Sample
-- honest Root norm. stamped on same z!`
local notation "YA" s:arg=> ⇑(checkedT U (ratioTo S n ℓ) (Yq s) (X s))
include hi hn hY
lemma stoke (hx:∀ u:Pr,∀ x V, Hom (σ u) (Yq u x V))
    (hY0:∀ t:Pr,t ≠ P→∀ b:Cover,Cylinder.Action.adj (κ t).pos (Yq (μT t) b)= Yq t ((κ t).flip.act b)):∃ (m:ℕ)(f:Fin m→Hole (Site (S.side R p)) S ℓ ℓ), Quills.crest f=Finset.univ ∧ Injective f ∧ m=Fintype.card (Site (S.side R p)) ∧ ‖A.regulator.average (CardsT.rolledT X (fun _=>U) Yq m f)‖=topH (sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z) A.regulator ⇑(checkedT U (ratioTo S n ℓ) (Yq P) x) P ^ Fintype.card (Site (S.side R p)):=by
    obtain ⟨C,hC,hT⟩:=juried z hj hp P (j:=n)
    have ht(u:Pr)(h:u≠P): YA u=tallH ((sky S R p n (hj.trans (hi.trans hn)) (evenW S R hp p) z).bandCut (Pv u).1 (Pv u).2) (YA (μT u)):=by
         apply CardsT.rentsG z hj hp P x U Yq hi hn u C hC hT h ?_ (hY u)
         rw[hT u]; exact hY0 u h
 
    rw [show checkedT U (ratioTo S n ℓ) (Yq P) x=checkedT U (ratioTo S n ℓ) (Yq P) (X P) from congr_arg _ (Tess.spec (mural (viewW S R hj) (evenW S R hp p) z) P rfl x rfl).symm]; apply orderedR A z hj hp P x U Yq hi hn ?_ ht
    let v:Hole (Site (S.side R p)) S ℓ ℓ:=⟨P,0,Lattice.center_box _⟩; refine ⟨σ P, ?_⟩
    intro V; have hz:= expert (R:=R) (ℓ:=ℓ) (I:=Pr) (Pilgrim.bout T P rfl x) Yq (fun _=>U) σ hx (hi.trans hn) le_rfl v V -- signature
    rw[CardsT.firstE ..] at hz; exact hz
omit hi hn hY
open Massive.Poised Massive.Poised.Plans Massive.Patria
variable (d:ℕ)(η:Massive.SourceRead.TaperHol) (sym:Massive.UV.RawSym)(B:Bore d)(hR:Rubric sym B) (Vg:Massive.UV.Label d) (Q':PatchMix d)(lb:ℕ)(hP:OrderMix A η sym B (i:=lb) Q') (q:Bool)(he:moored Vg.val q)
noncomputable abbrev readyT(c:Site (S.side R p)):= Hub.spine sym Vg (Hymnal.reversa T P c)
local notation "pB" a:arg=> readyT z hj hp P d sym Vg a
local notation "Yc" => fun (c:Pr)(b:Cover)=> B (S.side R n) b (Q' U (pB c))
lemma readySelf : pB P=Vg:=by unfold readyT Hymnal.reversa; rw [Pilgrim.at_p T P]; rfl
include hP hR he
lemma sparkY(hn:ℓ≤n)(hf:Vg≠0):∃ (m:ℕ)(f:Fin m→Hole (Site (S.side R p)) S ℓ ℓ), Quills.crest f=Finset.univ ∧ Injective f ∧ m=Fintype.card (Site (S.side R p)) ∧ ‖A.regulator.average (CardsT.rolledT X (fun _=>U) Yc m f)‖=topH (sky S R p n (hj.trans hn) (evenW S R hp p) z) A.regulator ⇑(checkedT U (ratioTo S n ℓ) (fun b=> B _ b (Q' U Vg)) x) P ^ Fintype.card (Site (S.side R p)):=by
     let B_:=(Yc);
     have hY : B_ P=(fun b=>B _ b (Q' U Vg)):=by funext b; dsimp only [B_]; rw [readySelf]
     rw [← hY]
     apply stoke A z hj hp P x (fun _=>q) U B_ le_rfl hn (fun v a b=> hR.advances _ (Q' U (pB v)) a b)
     · exact fun u b V => Hub.fade B sym hR (Q' U (pB u)) q (Depth.mooredMix η sym _ _ B A _ hP (Hub.toured sym Vg q he (Hymnal.reversa T P u) hf).1 U) b V
     intro t hh b; dsimp only [B_]; unfold readyT; have hm: (κ t).pos=(Pv t).2:=rfl
     rw [Hymnal.writes (T) P _ hh]
     rw (transparency:=.default) [hR.eye _ _ b (κ t).pos,hP.eyeO]; rfl
end CardsT
end YM.Intag
#print axioms YM.Intag.CardsT.sparkY
