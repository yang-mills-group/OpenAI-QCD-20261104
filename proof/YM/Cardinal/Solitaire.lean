import YM.Cardinal.Pockets
import YM.VMarker.Payout
import YM.VMarker.Cents
import YM.QCD.High.Saline
/-! # Singleton report tape, parity generalized. With mask bill requiring on-mask sizes only. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
namespace Card
namespace Iris
abbrev alpha:=Unit -- input and output.Lean rfl
abbrev topM :Finset alpha:= {()}
abbrev goldM (q:Bool):= burst (fun _=>q) topM
lemma engr (q:Bool): shade (goldM q)=q:=Ribbon.flavor (fun _=>q) () -- name
lemma engaged (q:Bool):(goldM q).Nonempty:=burstPos _ (singleton_nonempty _)
variable (N)(o:Site c) (q: Bool) (x:Iris.alpha)
local notation "M"=> Ribbon.ample N Unit
local notation "T"=> topM
local notation "Vk"=> goldM q
local notation "r"=> fun (_:Iris.alpha)=>q
local notation "K"=> Keys c N
local notation "R"=> Spine Iris.alpha
local notation "B!"=>Patio (Keys c N ⊕ Spine Unit)
local notation "p!"=>pluck K (goldM q)
set_option quotPrecheck false
abbrev moon (X:Grid c→Lat.Fields c N) (q:Bool):Prop:=∀ i,Hom q (X i)
-- marked positive
noncomputable def radiant (F:Grid c→Lat.Fields c N)(hp:moon N F q)(U:Grid c): B! := ⟨stake K Vk (F U), even_stake (goldM q) _ ((engr q).symm ▸ hp U)⟩
variable (F:Grid c→ Lat.Fields c N)(h:moon N F q)
local notation "w'"=>radiant N q F h
lemma worthG (i:Grid c) : pluck K (goldM q) (w' i)= F i:= quid ..
lemma worthE (i:Grid c) : Polite (fun _:alpha=>q) topM (w' i):=⟨_,rfl⟩
lemma badge (D:Finset (Spine alpha))(x y:B!)(hd:D=goldM q)(hx:Polite (fun _:alpha=>q) topM x)(hy:Polite (fun _:alpha=>q) topM y) : pluck K D x=pluck K D y→x=y:=fun h=>pluckVisible K x y fun i=>by
   subst D; by_cases he : i=goldM q; · exact he.symm ▸ h
   exact (hx.spectral _ he).trans (hy.spectral _ he).symm
lemma starless (x:B!)(hp:Polite (fun _:alpha=>q) topM x) : vacR R K x=0:= Subtype.ext ((revive ..).trans (hp.spectral _ (engaged q).ne_empty.symm))
lemma sphere (Y:Support c)(hp:∃ S:Support c,S⊆Y∧ LocalOn S F) (V': Grid c) (k: Lat.Frame c)(hF:Measurable F)(hl:∀ i,F i∈region (limits Y))(hQ:slots N k (F (gauge k V'))=F V') :
    Measurable (radiant N q F h) ∧ LocalOn Y (w') ∧ Stitch.lights topM Y (fun _=>o) (fun _=>q) (w' V')∧ parcelColor N k alpha (w' (gauge k V'))= w' V':=by
    obtain ⟨s,hs,hh⟩:=hp; refine ⟨?_,fun i j hp=> Subtype.ext (congr_arg (stake K Vk) (hh i j (agrees_mono hp hs))), ⟨worthE _ _ _ h _,?_⟩,?_⟩
    · exact ((stake K Vk).measurable.comp hF).subtype_mk
    · intro i; change scrape K i (stake K Vk (F V'))∈_; rw [stakesX]; split
      · exact hl _
      exact Subalgebra.zero_mem _
    apply badge N q Vk _ _ rfl _ _
    · rw [partColor, worthG, worthG,hQ]
    · exact vault N (fun _:alpha=>q) topM _ k (worthE _ _ _ h _)
    exact worthE _ _ _ h _ -- order apply proof goals check
lemma charge (u: B!)(hp:Polite (fun _:alpha=>q) topM u)(s:ℝ)(he:0<s): ‖token c M s (banknote N (fun _:alpha=>o) s u)‖= Creek.load (fun _=>s) (pluck K (goldM q) u):=by
     rw [Loom.pulse,withdrawCost N (fun _=>o) s he,sum_eq_single Vk]; intro i _ hi; rw [show pluck K i u=0 from hp.spectral _ hi]; exact load_zero _
     simp
lemma charged (S:Support c)(hp: ∀ x,F x∈region (limits S))(s:ℝ)(hs:o∈ S)(U:Grid c): Gated S (banknote N (fun _:alpha=>o) s (w' U)):=entitled N (fun _=>o) s S Vk (F U) (hp U) fun _ _=> hs
-- general Puff
structure Puff (c:Side)(N:ℕ)(I:Type)(q:Bool) where
    addr:I→RegularAddress c
    fill : I→Grid c→Lat.Fields c N
    beams :∀ i,moon N (fill i) q
namespace Puff
variable {q}(X:Puff c N J q)
noncomputable def roll : Reel c N Unit J:= ⟨X.addr, fun _=>T,fun i=> radiant N q (X.fill i) (X.beams i)⟩
structure Seal (p:Site c)(F:Puff c N J q) :Prop where
    anchor i:(F.addr i).site=p
    stays i: LocalOn (F.addr i).support (F.fill i)
    label i: Measurable (F.fill i)
    shade i U k: slots N k (F.fill i (Lattice.gauge k U))= F.fill i U
    sees i x:F.fill i x∈ region (limits (F.addr i).support)
-- eligibility.
variable (he: Seal N o X)
include he
set_option maxRecDepth 6000 in
lemma declare : X.roll.Book (fun _=>o) (fun _=>q) :=by
    let F:= roll N X -- maybe Roll argument
    have heQ(i V k):= sphere N o q _ (X.beams i) _ ⟨_,Subset.refl _,he.stays _⟩ V k (he.label i) (he.sees i) (he.shade i V k)
    refine ⟨fun i=>singleton_nonempty _,fun i=>?_,fun i=>(heQ i 1 1).1,fun i=> (heQ i 1 1).2.1,fun i V=> (heQ i V 1).2.2.1,?_⟩
    · change image (fun _:Unit=>o) topM⊆_; rw [topM,image_singleton]; exact singleton_subset_iff.mpr ((he.anchor _ ) ▸ (X.addr i).anchor) -- rw he anchor local proof
    intro i U k; exact (heQ i (show Grid c from U) (show Frame c from k)).2.2.2
omit he
lemma reads (i:J) : Reel.speaker (fun _:alpha=>q) (X.roll) i=X.fill i:=funext (worthG _ _ _ (X.beams i))
end Puff
end Iris
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.Iris.Puff.declare
