import YM.QCD.Spice.Lemon
/-! # Zig(Z) physical tip before coating Flaps. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Spice
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open Lat Kit Grass Brick Cove Stew ConnectedActivityE6.Blaze Push.Uniform
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio} {L:Side}
    {P B : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v R : ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j : ℕ} {D : Slab su c l} {q : Chi} {d u : ℝ} {f' : Config su f → ℝ} {H:Grid f→EvenA f N}
variable (a:Museum F x A X Y I) [Fintype I] {C:Libretto su n}{E:Record} {ε:ℝ}
    (hp:Plays C E P B Pt T x) (hg :Canvas P (S.ratio.parent o) (reach x) V g n C.C)
variable (hz:Short S B X)(hk:1≤n)(ho:o∈X)(hV: Healthy P.threshold Y V) (U:Config su f)(hu:0 ≤u)
local notation "Z"=> a.received k T q d u V U 0
local notation "W'"=> loom P (reach x) C.C
include hp hg hz hk ho hu
lemma printing (ht:∀ x:su.Color, ‖x‖≤ ε → su.chord (su.lieExp x)≤ ρ*‖x‖)(hr:0 ≤ ρ)(hQ:E.Q * loom P (reach x) C.C ≤ ε)(hM:C.M*loom P (reach x) C.C ≤ ε) :
 BeamRaw X (gauge (g ∘ S.ratio.parent) (a.received k T q d u V U 0)) 1 (ρ*(loom P (reach x) C.C)*(E.Q+C.M+C.M)):=by
    let v:= W'; let o':= S.ratio.parent o; let D':Slab su c 0:=0; let w:Prices su I:=0; let p:= enters V o' (reach x) g D' (a.extra g u w); have hh:=hp.rehearsed.tensions
    have hv:0 ≤v:=by unfold v loom; positivity [C.C_one,P.threshold_pos]
    have he: ‖a.extra g u w‖ ≤v:= (a.extra_size g u hu w).trans (by rw [show tape w=(0:LogArray su I) from rfl,norm_zero,mul_zero]; exact hv)
    have h := (depicted (d:=d) (q:=q) a hp.bulletin hp.rehearsed.weft (hp.acts F k) hz hg ho C.C_one hh.allows U w he D').self_of_nhds
    let g':= gauge (g ∘ S.ratio.parent) (a.received k T q d u V U 0)
    rw [Sample.journey_origin] at h; let φ' := φ T F true (p 0).1; let f':=display T F x k true (p 0); let F' i:=su.lieExp (φ' i)
    have h0: ‖p 0‖ ≤v:=max_le ((congr_arg (‖·‖) (launch_zero D' (V:=V) (g:=g) (o:=o') (r:=reach x))).trans_le (hg.paid C.C_one)) he
    have hm Y : su.chord (F' Y) ≤ ρ*(C.M*v):=by
       have hf:=Dust.taxes C hp hg hk (F:=F) (D:=D') (fun i=> i.elim0) (Nat.zero_le _); have hY : ‖φ' Y‖ ≤ C.M*v:= (norm_le_pi_norm φ' Y).trans (by simpa only [norm_iteratedFDeriv_zero] using hf.pay 0 (Nat.zero_le _)); exact (ht _ (hY.trans hM)).trans (mul_le_mul_of_nonneg_left hY hr)
    intro i hi hj; have hx:= h i (show i.1∈(inspected X:Set (Site f)) from Finset.mem_union_left _ hi) (show i.1+step i.2∈(inspected X:Set (Site f)) from Finset.mem_union_left _ hj) -- edit
    have hy : g' i=(F' i.1)⁻¹ *su.lieExp (f' i)*F' (i.1 +step i.2):=by
       rw [show su.lieExp (f' i)=F' i.1 * g' i*(F' (i.1+step i.2))⁻¹ from (mul_one _).symm.trans hx]; group

    change su.chord (g' i*1⁻¹)≤_; rw [inv_one,mul_one,hy]; have hh₁: ‖f' i‖ ≤ E.Q*v:= (norm_le_pi_norm f' _).trans (display_price (hp.acts _ _) hk h0 hh.allows.le E.majorant)
    have hY: su.chord ((F' i.1)⁻¹ *su.lieExp (f' i)) ≤ ρ*(C.M*v) +ρ*(E.Q*v):=by apply (su.chord_triangle ..).trans; rw [su.chord_inv]; exact add_le_add (hm _) ((ht _ (hh₁.trans hQ)).trans (mul_le_mul_of_nonneg_left hh₁ hr))
    apply (su.chord_triangle ..).trans; apply (add_le_add hY (hm _)).trans_eq; unfold v; ring
end YM.QCD.Spice
