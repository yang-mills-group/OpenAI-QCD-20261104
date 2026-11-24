import YM.Cardinal.Beau
/-! # Applying an actual extra marked soft operation, and restoring unmarked Rail. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f L:Side}{m k l N:ℕ} {I J U E:Type}[Fintype I]
variable {a A C v w t t₁ t₂:ℝ}{O: BudgetPoint}
variable (N)(p:I→Site c)(q:I→Bool)(θ φ r:ℝ)
local notation "M"=> Ribbon.ample N I
variable (Y: Ruby.Hue c (ample N I) J)(F: Patron.Rail c (ample N I) U)
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "b!"=> banknote N p θ
local notation "d!"=> withdraw N p θ
local notation "T!"=> Trail Y F t
namespace Card
set_option quotPrecheck false
open QCD.Villa QCD.Leaf QCD.Loom QCD.Loom.Fleet QCD.Stew QCD.High QCD.Acre QCD.Meridians QCD.Kites
local notation "bz"=> O.threshold
local notation "Vt"=> (vacR R K).comp (withdraw N p θ)
open Relation
-- property through L.Fleet. Any marker layout with cuffs. costs true irrespective of circumference. Can then reissue from bridge Hill with bigger approach heights.This is needed also with deletion.
def atlas (P:I → Support c)(x:Support c): Finset I:= Finset.univ.filter (fun i=>P i ⊆ x)
lemma atlasNear {A B:Support c}(P:I→Support c)(h:A⊆B): atlas P A ⊆atlas P B:=fun i hi=> mem_filter.mpr ⟨mem_univ _,Subset.trans ((mem_filter.mp hi).2) h⟩
variable (Q':I→Support c)
structure Gully (P:I→Support c) (F:Patron.Rail c (ample N I) U):Prop where
    vfs (i:U)(V:Grid c) : ValidPieces (Keys c N) q (atlas P (F.addr i).place) (withdraw N p θ (F.warp i V))
lemma validTurn (X: Patio (Keys c N⊕Spine I))(L:Finset I)(h:ValidPieces (Keys c N) q L X) : ValidPieces K q L (turn I r X):=by rw [h.wholeV,map_sum]; exact ValidPieces.cost _ _ (fun i hi=> ValidPieces.role _ (cloak r i _ q (choseTuft ..)) (mem_powerset.mp ((mem_filter.mp hi).2)))
local notation "W"=> ValidPieces K q
lemma pumpG (P:Ruby.Hue c N J)(h:Gully N p q θ Q' F)(hv:0<φ) : Gully N p q φ Q' (limb N p φ θ r P F t):=by
    let b:= pursue N p φ F θ r; let A:= radial I P; let K':= withdraw N p φ; refine ⟨fun i V=>?_⟩; let m:= atlas Q' (scopeK A b i.val); change W m (K' (payer ..)); unfold payer; split; swap; · rw [map_zero]; exact ValidPieces.noneV
    rw [map_prod]; have he (T:Finset _) (F:Stamp J U→ Patio (Keys c N⊕Spine I))(hp:∀ j∈T,W m (F j)) : W m (∏ i∈T,F i):= Subalgebra.prod_mem (ValidPieces.course q m) hp -- explicit args test
    apply he; intro j hj; have ht:footD A b j⊆ scopeK A b i.val:= subset_biUnion_of_mem _ hj
    rcases j with j|j
    · change W m (K' (changeBill N p r θ φ (F.warp j V))); rw [show K' _=_ from changeLife N p φ θ r (F.warp j V) hv]; exact validTurn N q r _ _ ((h.vfs ..).raise (atlasNear Q' ht)) -- args order maybe θ
    change W m (K' (NormedSpace.exp (A.mean j V)-1)); rw [map_sub,map_one,map_exp K' K'.toLinearMap.toContinuousLinearMap.continuous,sub_eq_add_neg, show A.mean j V= banknote N p φ (rootR R K (P.mean j V)) from (real_sector ..).symm, Cupola.home N p φ hv]; apply ValidPieces.plus _ ValidPieces.oneV.minus; apply ValidPieces.exponent; refine ValidPieces.role ∅ ?_ (empty_subset _); unfold Polite; rw [burst_absent]; exact ⟨_,quiet ..⟩
variable (p':I→Site c)
noncomputable def revise : EvenA c (ample N I)→ₐ[ℂ] EvenA c (ample N I):=(banknote N p' θ).comp (withdraw N p θ)
noncomputable def coming := valH M (revise N p θ p') F -- valH needs J type and maybe p. 
local notation "P₀"=> coming N p θ F p'
local notation "b₀"=> banknote N p' θ
local notation "d₀"=> withdraw N p' θ
local notation "tQ"=> revise N p θ p'
lemma revMap (hp:0 < θ) (x:EvenA c (ample N I)) : withdraw N p' θ (revise N p θ p' x)=withdraw N p θ x:= Cupola.home N p' θ hp _
lemma revGrace (hp:0 < θ)(V: Lat.Frame c)(x:EvenA c (ample N I))(h: Well N p θ q x) : revise N p θ p' (sways (Lat.rotates (ample N I) V) x)=sways (Lat.rotates (ample N I) V) (tQ x):=by
   let y:= d! x; have hV:= (congr_arg _ h.spark.symm).trans (all_color N p θ q V y h.applies).symm -- congr arg inferred? 
   refine Eq.trans (congr_arg _ (show sways (Lat.rotates M V) x= _ from hV)) ?_
   rw [show tQ _= b₀ (parcelColor N V I y) from congr_arg b₀ (Cupola.home N p θ hp _)]; exact all_color N p' θ q V y h.applies
variable (hT:Wage.Tip N p q F O θ a w)(hp:1≤θ)(hv:1≤w)(hQ:Gully N p q θ Q' F)(hx:∀ i,p' i ∈ Q' i)
include hT hp
lemma gloss (i:U)(V: Grid c): ‖token c M θ ((P₀).warp i V)‖= ‖token c M θ (F.warp i V)‖:=by
    have ht:= (hT.fits i V).spark; let x:= d! (F.warp i V); change ‖token _ _ _ (banknote N p' θ x)‖= _; rw [Loom.pulse,Loom.pulse,← show banknote N p θ x=F.warp i V from ht]; exact (withdrawCost N p' θ (zero_lt_one.trans_le hp) _).trans (withdrawCost N p θ (zero_lt_one.trans_le hp) _).symm
include hQ hx
lemma changed_tip : Wage.Tip N p' q P₀ O θ a w:=by
    let Z:= hT.tilt; have hZ := Z.uses; let r:=revise N p θ p'; let F':= coming N p θ F p'; have hθ:=zero_lt_one.trans_le hp
    refine ⟨⟨⟨fun i U V hv hQ=>congr_arg r (hZ.uses i U V hv hQ), fun i=>r.toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hZ.reads i),fun i U=>?_,fun i U hh=>hZ.buys i U (fun he=> hh ((congr_arg r he).trans (map_zero _)))⟩,fun i U k=>?_,?_⟩,fun i V=>⟨show b₀ _=b₀ _ from congr_arg b₀ (revMap N p θ p' hθ (F.warp i V)), (revMap N p θ p' hθ (F.warp i V)).symm ▸ (hT.fits i V).applies⟩⟩
    · let X:= (F.addr i).place; let x:= F.warp i U; let P:=(hQ.vfs i U); change Gated X (b₀ (d! x)); have he:= P.wholeV; rw [show d! x=_ from he,map_sum]; unfold Gated; rw [map_sum]; apply Subalgebra.sum_mem -- check
      intro j hj; let z:=(pick K q j (d! x)).val; let v:= burst q j; have hz:z=stake K v (pluck K v (d! x)):= rfl; change pen N p' θ z∈_; rw [hz]; apply entitled N p' θ _ _ _ (pennied N p θ v x X (hZ.role ..)); intro m hm; exact ((mem_filter.mp (mem_powerset.mp ((mem_filter.mp hj).2) (located q _ _ hm))).2 (hx _)) -- located collision
    · exact congr_arg Subtype.val ((revGrace N p q θ p' hθ k _ (hT.fits ..)).symm.trans (congr_arg r (Subtype.ext (Z.pigment i U k))))
    obtain ⟨f,hf,hV⟩:= Z.sold.cost; exact ⟨f,hf,fun i V=> (gloss N p q θ F p' hT hp i V).trans_le (hV i V)⟩
omit hQ hx
include hv
lemma revVolume (V:Grid c)(hz:0 ≤ a): withdraw N p' θ (heartK P₀ O.threshold V)=d! (heartK F O.threshold V):=by
    let R':=revise N p θ p'; refine Eq.trans (congr_arg _ ?_) (revMap N p θ p' (zero_lt_one.trans_le hp) _);
    unfold Kites.heartK; change _= R'.toLinearMap.toContinuousLinearMap _; rw [ContinuousLinearMap.map_tsum _ (profits F V hp hv hT.tilt.sold hz _)]; apply tsum_congr; intro i; change tK P₀ _ _ i=R' _; unfold Ruby.tK; split; next h=>rw [if_pos (show separated (blocked (Ruby.home F)) i ∧ flags O.threshold V = i.biUnion (oriD F) from h)]; exact (map_prod R' ..).symm
    next h=> rw [if_neg (show ¬(separated (blocked (Ruby.home F)) i ∧ flags O.threshold V = i.biUnion (oriD F)) from h)]; exact (map_zero R').symm
omit hT hp hv
lemma transit (h:0<θ): faultK N p θ F=faultK N p' θ P₀:=by
   have he {U:Type}(F G: Patron.Rail c N U)(ht:F.addr=G.addr)(hp: F.warp=G.warp):F=G:=by cases F; cases G; congr
   exact he _ _ rfl (funext fun i=> funext fun V=> congr_arg (vacR R K) (revMap N p θ p' h _).symm)
end Card
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Card.changed_tip
