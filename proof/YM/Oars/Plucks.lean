import YM.Oars.Mergers
import YM.Cardinal.Effect
/-! # Insert single Example Puff across genuine multi alph. preserving all Re+Rail proofs.
    no assumption from masked footprints.J -/
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
namespace Stags
open Card Card.Iris Sample
open Kit Kites ConnectedActivityE6 Pressure
variable {D: I→Type}(b:I)
noncomputable abbrev amber (b:I) := Sample.flame (Keys c N) (fun _:Iris.alpha=>q b) q (fun (_:Iris.alpha)=> some b) (fun _ _=>1)
-- argument order. inject singleton.V sale.
local notation "↑J"=> amber (c:=c) N q b
local notation "L₀"=>goldM (q b)
set_option quotPrecheck false
local notation "M⁺"=> burst q {b}
local notation "p!"=> fun (_:Iris.alpha)=> p b
local notation "q0"=> fun (_:Unit)=> q b
variable (Y:Puff c N J (q b))(h:Puff.Seal N (p b) Y)
lemma goldMap (x:Patio (Keys c N⊕Spine Unit))(hp:Polite q0 topM x) : (↑J x).val= stake K (burst q ({b}:Finset I)) (pluck K (goldM (q b)) x):=by
    let W' :=fun (_: Iris.alpha)=> some b; let C:= Sample.leaves K (fun (_:Iris.alpha)=>q b) q W' (fun _ _=>1); change C x.val= _; nth_rw 1 [← hp.exact]; unfold C; rw [markedOut,map_mul,Sample.leaving K (fun (_:Iris.alpha)=>q b) q W' (fun _ _=>1) () b rfl rfl]; unfold Sample.leaves; rw [show ((↑((fun j=>fun i:I=>(1:ℝ)) () b):ℂ)=(1:ℂ)) from (by simp),one_smul,AlgHom.comp_apply,tarfib,blot_left,markedOut]; rfl
lemma goldPay (x:Patio (Keys c N⊕Spine Unit))(hp:Polite q0 topM x) : Polite q ({b}:Finset I) (↑J x) ∧ pluck K (burst q {b}) (↑J x)=pluck K (goldM (q b)) x:=by
    have ht:= goldMap N q b x hp; exact ⟨⟨_,ht.symm⟩,(congr_arg (scrape K (burst q {b})) ht).trans (quid ..)⟩
lemma goldColor (x:Patio (Keys c N⊕Spine Unit))(hp:Polite q0 topM x) (k: Frame c): parcelColor N k I (↑J x) = ↑J (parcelColor N k Unit x):=by
    apply pluckVisible; intro s; have h:=(goldPay N q b x hp); let y:= parcelColor N k Unit x; have hx:= goldPay N q b y (vault N q0 topM x k hp); by_cases H:s= M⁺; · subst s; rw [partColor,h.2,hx.2]; exact (partColor ..).symm
    rw [partColor,show pluck _ _ _=0 from h.1.spectral s H,map_zero]; exact (hx.1.spectral s H).symm
noncomputable def burstY: Reel c N I J:=⟨Y.addr,fun _=>{b}, fun i V=>↑J ((Y.roll).mark i V)⟩
local notation "Σ'"=> burstY N q b Y
include h
lemma burstP : (Σ').Book p q:=by
    have hp:=Puff.declare N _ Y h; refine ⟨fun _=>singleton_nonempty _,fun i=>by simp only [show (Σ').z i={b} from rfl,image_singleton]; exact singleton_subset_iff.mpr ((h.anchor i) ▸ (Y.addr i).anchor),fun i=> (↑J).toLinearMap.continuous_of_finiteDimensional.measurable.comp (hp.permit _), fun i U V he=> congr_arg (↑J) (hp.room i U V he),fun i V=>?_,fun i U k=>?_⟩
    · let x:= Y.roll.mark i V; have hY:=goldPay N q b x (hp.stage i V|>.1); refine ⟨hY.1,fun s=>?_⟩
      by_cases H:s= M⁺; · subst s; exact hY.2.symm ▸ (hp.stage i V).2 _ -- subst goal Meta.Freeze
      change scrape K s (↑J x).val ∈ _; rw [hY.1.spectral _ H]; exact Subalgebra.zero_mem _
    exact (goldColor N q b _ (hp.stage i _).1 k).trans (congr_arg _ (hp.tint i U k))
omit h
lemma burstReads (i:J) : Reel.speaker q Σ' i=Y.fill i:= funext fun V=> (goldPay N q b _ (worthE N _ _ (Y.beams i) V)).2.trans (worthG N _ _ (Y.beams i) V)
-- Wax.J Hue forward at prices
variable (W: Ruby.Hue c (ample N Unit) E)(hq:∀ i V,Mint N (fun _:Unit=>p b) θ (fun _:Unit=>q b) Iris.topM (W.mean i V))
local notation "↑p!"=> banknote N (p!) θ
local notation "↓b!"=> withdraw N (p!) θ
include hq
noncomputable def baptism : Ruby.Hue c (ample N I) E:= ⟨W.bud,fun i V=> b! (↑J (↓b! (W.mean i V)))⟩
local notation "κ"=>baptism N p q θ b W
lemma baptismRead (i:E)(V:Grid c)(ht:0<θ) : d! ((κ).mean i V)= ↑J (↓b! (W.mean i V)):= Cupola.home N p θ ht _
variable (he: Wax W O.threshold O.B a A θ)(hc:∀ i,shadeG (W.mean i))(ht:1 ≤ θ)(hψ: ∀ i,p b ∈ W.bud i)
include he hc ht hψ
lemma lustre : Wax κ O.threshold O.B a A θ ∧ ∀ i, shadeG ((κ).mean i) ∧ ∀ V,Mint N p θ q ({b}:Finset I) ((κ).mean i V):=by
    let D:= (b!).comp ((↑J).comp (↓b!)); have hp:= he.burns; have hh:0 < θ:= zero_lt_one.trans_le ht; let x i V:= ↓b! (W.mean i V); have hv i V:=goldPay N q b (x i V) (hq i V).shows
    refine ⟨⟨⟨fun i V Z hl hP=>congr_arg D (hp.bond i V Z hl hP),fun i=>D.toLinearMap.toContinuousLinearMap.continuous.measurable.comp (hp.meas i),fun i U he hV=>he ((congr_arg D (by_contra fun hf=> hp.non i U hf hV)).trans (map_zero _)),fun i V=>?_⟩,?_⟩, fun i=> ⟨?_,fun V=> Mint.initiate _ hh _ (hv i V).1⟩⟩
    · change pen N p θ (↑J (x i V)).val ∈region _; rw [goldMap N q b _ (hq i V).shows]; apply entitled; exact (pennied N (fun _:Unit=>p b) θ L₀ _ _ (hp.lives i V)); intro j hj; have hx : j.1.1=b:=mem_singleton.mp (located q {b} j hj); rw [hx]; exact hψ i
    · obtain ⟨f,hF,hY⟩:=he.expense; refine ⟨f,hF,fun i V=>?_⟩; let z:=x i V; let y:= ↑J z; have hl:= hq i V
      apply le_trans _ (hY i V); rw [← show ↑p! z=W.mean i V from hl.spark]; -- probably rewrite misses.
      change ‖Loom.token c (ample N I) θ (b! y)‖ ≤ _; rw [Loom.pulse,withdrawCost N p θ hh,sum_eq_single M⁺]; swap
      · intro j _ hj; rw [show pluck _ _ y=0 from (hv i V).1.spectral j hj,Cove.load_zero]
      rotate_left; · simp
      rw [show pluck K M⁺ y=pluck K L₀ z from (hv i V).2]; exact le_of_eq (by rw [Card.Iris.charge N (p b) (q b) z hl.shows θ hh]) -- hh unused.ht field.
    · intro V k; let s:=W.mean i (Lattice.gauge k V); let u:= x i (Lattice.gauge k V); have hx : parcelColor N k Unit u=x i V:=by
          rw [← Cupola.home N (fun _:Unit=>p b) θ hh (parcelColor N k Unit u)]; apply congr_arg (↓b!); exact (across N (fun _:Unit=>p b) θ (fun _=>q b) topM k u (hq i _).shows).trans ((congr_arg (sways _) (show banknote N (fun _:Unit=>p b) θ u=s from (hq ..).spark)).trans (Subtype.ext (hc i V k)))
      refine congr_arg Subtype.val (?_: sways _ (b! (↑J u))=b! (↑J (x i V))); rw [← Cupola.across _ _ _ q {b} _ _ (hv i _).1,goldColor N q b u (hq i _).shows k,hx]
end Stags
end YM.MassiveQCD.Plate
#print axioms YM.MassiveQCD.Plate.Stags.lustre
