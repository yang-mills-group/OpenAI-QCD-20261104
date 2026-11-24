import YM.MassiveQCD.Cupola.Wood
import YM.MassiveQCD.Plate.Pepper
/-!
# Native marks at K-Life stage (honest budgets incl all multiplicity)
 K entries only exist for nonempty marker set; no conflict-free activation assumption
 beyond aperture S; consume with genuine unmarked. Bookkeeping value non-geared by
 terminal units; publisher stores raw physical coefficient data (COUNTING here arbitrary
 units possible by choosing amount factors at initial etc.). On every calculation supply
 *billing radius* or bill repeat coordinates explicitly; a currency change with each
 successor clock doesn't relabel the signs or supports. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Plate
open QCD Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Relight Ruby
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{k B N:ℕ}{s t h θ η α:ℝ}{U I E:Type}[Fintype I]
structure Film (c:Side)(N:ℕ)(I:Type)[Fintype I](U:Type) where
 addr : U→ Cove.Hat c
 z : U→ Finset I
 mark : U→ Grid c→Patio (Keys c N⊕Spine I)
namespace Film
local notation "K"=> Keys c N
local notation "R"=> Spine I
local notation "pay"=> Keys c N⊕Spine I
variable (N)(p:I→Site c)(q:I→Bool) (M : Film c N I U)
structure Beat (t:ℝ) :Prop where
    commits i: (M.z i).Nonempty
    spark i: (M.z i).image p⊆ (M.addr i).place
    matters i: Measurable (M.mark i)
    reads i: UsesFinal t (M.addr i).place (M.mark i)
    color i U g: parcelColor N g I (M.mark i (Lattice.gauge g U))= M.mark i U
    mask i U (h :M.mark i U≠0): RG.flags t U∩(M.addr i).place=(M.addr i).inv
    budget i V: Stitch.lights (M.z i) (M.addr i).place p q (M.mark i V)
       -- Polite etc
-- actual combined charges use load not dimension loss.Film.All.Time.
noncomputable def glyph (V:Grid c)(i:U) (w:ℝ) :ℝ:= load (Stitch.Tablet.chip w K R) (light _ (M.mark i V)) -- locate
-- weighed by rates all
noncomputable def fares (p:U→ℝ)(w:I→ℝ)(τ:ℝ):U→ℝ:=GasP.taxed (fun i=>(M.addr i).inv) (fun i=>(∏ j∈(M.z i), |w j|)*p i) τ
structure Stock (B:ℕ)(τ η θ C:ℝ)(w:I→ℝ) :Prop where
    price:∃ b:U→ℝ,(∀ i U', glyph N M U' i θ ≤ b i) ∧ Ac.Hit (fun i=>(M.addr i).place) B (fares N M b w τ) η C -- Binder order.Y?
variable (F:Patron.Rail c (ample N I) U) (A:Set (Finset I))(φ:ℝ)
noncomputable def seats (x:Cove.Hat c): Finset (Finset I):= Finset.univ.filter (fun i=> i∈A ∧ i.Nonempty ∧ i.image p⊆ x.place)
noncomputable abbrev Seats := Σ i:U, ↥(seats p A (F.addr i)) -- include F etc
local notation "St"=> Seats N p F A
noncomputable def publication: Film c N I (Seats N p F A):=⟨F.addr ∘ Sigma.fst, fun i=> i.snd.val,fun i U=> Cupola.pick (Keys c N) q i.snd.val (withdraw N p φ (F.warp i.fst U))⟩
local notation "S!"=> publication N p q F A φ
private lemma pantry (x:EvenA c (ample N I))(y:EvenA c (ample N I))(s:Finset I)(z: Lat.Frame c)(hf:0<φ)(ht: Well N p φ q x) (h:sways (Lat.rotates (ample N I) z) x=y) : parcelColor N z I (Cupola.pick K q s (withdraw N p φ x))=Cupola.pick K q s (withdraw N p φ y) :=by
    let P:=withdraw N p φ x; let V:=parcelColor N z I; let w:=(withdraw N p φ y); let t:= burst q s
    have hv:w=V P:= Eq.trans (congr_arg (withdraw N p φ) (Eq.trans h.symm ((congr_arg _ ht.spark.symm).trans (all_color N p φ q z _ ht.applies).symm))) (Cupola.home N p φ hf (V P)); change V _ =Cupola.pick _ q s w; rw [hv]; apply pluckVisible; intro i; rw [show pluck _ i (V _)=_ from partColor ..,Cupola.pick,many,many]; split; exact (partColor ..).symm; exact map_zero _
private lemma thee (t: Finset I)(x:EvenA c (ample N I))(o:Support c) (h:Gated o x) : clad (limits o) ((Cupola.pick K q t (withdraw N p φ x)).val):= by unfold clad; intro i; change pluck K i (chooseBlade K _ _)∈_; rw [many]; split; exact Cupola.pennied N p φ i x o h; exact Subalgebra.zero_mem _
lemma turned_t (h:Pill F t φ B η θ)(hv:∀ i V,Well N p φ q (F.warp i V))(hf:0<φ): Beat N p q S! t:=by
    refine ⟨fun i=> ((mem_filter.mp i.snd.2).2).2.1, fun i=> ((mem_filter.mp i.snd.2).2).2.2, ?_,?_,?_,?_,?_⟩
    · exact fun i=> (Cupola.pick K q _).measurable.comp (((withdraw N p φ).toLinearMap.toContinuousLinearMap).measurable.comp (h.uses.reads i.1))
    · exact fun i U V he hf=> congr_arg (fun x=>Cupola.pick K q _ (withdraw N p φ x)) (h.uses.uses i.1 U V he hf)
    · exact fun i U g=> pantry N p q φ _ _ i.snd.val g hf (hv i.1 _) (Subtype.ext (h.pigment i.1 U g))
    · exact fun i U hx=> h.uses.buys i.1 U (fun hp=>hx (by unfold publication; dsimp only; rw [hp,map_zero,map_zero]))
    exact fun i U=> ⟨choseTuft ..,thee N p q φ i.2.val _ _ (h.uses.role i.1 U)⟩
lemma cost_g (hf:0<φ)(i:St)(U:Grid c)(h:Well N p φ q (F.warp i.1 U)) : glyph N S! U i φ ≤ ‖token c (ample N I) φ (F.warp i.1 U)‖:=by
    let f:=F.warp i.1 U; let v:=i.snd.val; let x:=withdraw N p φ f
    have h₁: pluck K (burst q v) (Cupola.pick K q v x)=pluck K (burst q v) x:= (many ..).trans (if_pos rfl)
    refine Eq.trans_le ?_ (Well.pin (burst q v) hf h); change Stitch.Tablet.credits φ (Cupola.pick _ q v x)=load (fun _=>φ) (pluck K (burst q v) x); rw [Stitch.Tablet.polite_bill v _ (choseTuft ..) hf]; exact congr_arg _ h₁
-- instance.Seats countable, follow dependent compiler
instance [Countable U] : Countable (Seats N p F A) := by unfold Seats; infer_instance
end Film
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Film.cost_g
