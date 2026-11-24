import YM.QCD.Fawn.Tides
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Hera
open Heir
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Puff Push.SectorMeasure Exterior Planned.AtomRegular MeasureTheory AnalyticBridge.LocalGaussian.Moments
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {V : Config G c} {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
open Heir.Lute

open MultiNext.SignedSource.Ease
noncomputable def dueFee (C:Libretto G n)(P:BudgetPoint)(B:ℕ):= ripple C 1*(1+(1+(B:ℝ))^debited n P.power)
lemma tern {L:Side} (he:Lute.Plented C D P B L r x u) (hp: B.B≤ 2*radiusB x)(ht: P.threshold ≤ 2*B.threshold)(hu:0≤u)(hh:0≤τ) (M:ℕ)(hQ:coverNumber B.B X≤M): lyreFee C τ D P B L X r x u ≤ τ* dueFee C P M:=by
  have hx:= Lute.extra_le hp ht hu he (X:=X); let a:=(1+(coverNumber B.B X:ℝ))^debited n P.power
  have hv :0 ≤ ripple C τ:=mul_nonneg (by positivity [leading_one C]) hh
  apply (mul_le_mul_of_nonneg_left (add_le_add_right (hx.trans (show a ≤ (1+(M:ℝ))^debited n P.power by unfold a; gcongr)) 1) hv).trans_eq
  unfold dueFee ripple; ring
lemma wide {L:Side} (h:Lute.Plented C D P B L r x u) (hp: B.B≤ 2*radiusB x)(ht: P.threshold ≤ 2*B.threshold)(hu:0≤u)(hh:0≤τ) (M:ℕ)(hQ:coverNumber B.B X≤M)(hM:L.val ≤ M^3): lyreFee C τ D P B L X r x u ≤ (τ* dueFee C P M)* (1+(M:ℝ))^15 * (L.val:ℝ)⁻¹^5 :=by
   let w:=τ*dueFee C P M; have hw:0 ≤ w:= by unfold w dueFee ripple; positivity [Lute.leading_one C]
   have hh':0 < (L.val:ℝ):=by positivity
   apply (tern h hp ht hu hh M hQ).trans; rw [mul_assoc]; apply le_mul_of_one_le_right hw; rw [inv_pow (L.val:ℝ), ← div_eq_mul_inv,le_div_iff₀ (pow_pos hh' _),one_mul]; rw [show 15=3*5 from rfl,pow_mul]; apply pow_le_pow_left₀ hh'.le; exact_mod_cast hM.trans (Nat.pow_le_pow_left (Nat.le_add_left M 1) _)
lemma guise (Z : Rights G n) (a : Museum F x A X Y ι)(U : Config G f)(hp : Charm B X f')(ht:B.supBounds o X f' τ)(hk:o∈X)(h: Plays C D P B Pt T x)(hx:Healthy P.threshold Y V)(hu : 0≤u)(Γ)(hΓ:Silences G ι n u (D.ε*B.threshold) Γ)(k:S.Choices)(q:Chi)(d:ℝ)(r:ℕ) :
    Fugue a U f' T C D P B r Γ u (grandFee Z*τ) k q d o V:=by
    intro z hz; have hb:= h.rehearsed
    have hp:= jointE (q:=q) (d:=d) Z a h.bulletin (h.acts F k) (h.stages F) hk hp ht D.majorant C.matins hb.orders hb.temp_eq hb.powers U z hu h.sew C.width C.price hb.early C.web C.Z rfl hb.tensions hb.wire hb.weft (by rw [← hb.test]; exact le_trans (by norm_num) P.order_ge) h.space hx (hΓ.stay z hz)
    let ρ:= rust C D P B S.patch.L X r x u; have hw:0≤ρ:=rust_nn hu; let v':=loom P (reach x) C.C
    have he : Heir.segment n X P B D.Q C.M v'≤ ρ * powers z^2:=by
       refine le_trans (b:=ρ) ?_ (le_mul_of_one_le_right hw (one_le_pow₀ (grows z))); refine (le_add_of_nonneg_right (tranche_nn _ n (show 0 ≤ D.Q from zero_le_one.trans D.majorant) hu B.threshold_pos.le)).trans (le_add_of_nonneg_right (scratch_nn _)) -- implicit v'? inspect
    have hK: τ*grandFee Z≥0:= mul_nonneg ht.1 (mul_nonneg (patterns_nonneg _) (zero_le_one.trans Z.large))
    refine ⟨hp.1,fun l hl A hA=>?_⟩; apply (hp.2 l hl A hA).trans; rw [mul_right_comm]; apply mul_le_mul_of_nonneg_left _ (by rwa [mul_comm (grandFee Z) τ]) -- edit
    have hh:= ample_one n X P B D.majorant C.matins C.C_one (x:=x)
    apply pow_le_pow_left₀ (zero_le_one.trans hh); unfold ample; refine add_le_add ?_ he; unfold leading; apply le_add_of_nonneg_left; positivity
end YM.PhysicalNext.JointLoad.Hera
