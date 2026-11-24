import YM.QCD.Raft.Field

/-! # Projection to transverse representatives. legitimate on the real response; modes evaluated at actual frequencies. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Raft
open Lattice Wilson Function Finset Filter Metric RG Precision Bloch Laurent
open Extra Iteration QCD.Smoke Work.F08 Work.F03 Exterior Bid Push.Loops Matrix YM.Next.Free
open scoped Topology BigOperators Matrix ContDiff Classical InnerProductSpace
variable {c f n:Side}{L:Side}{p:Site n}{A:Momentum}
lemma loft (h:Matches A p) (z:ℂ): cmat (Exterior.d 0 n)*ᵥ vw p (fun _:TypeFace 0=>z)= vw p (fun i=> z* Exterior.q A (axisEquiv.symm i)) := by
  funext ⟨x,i⟩; obtain ⟨i,rfl⟩:= axisEquiv.surjective i
  let v:=vw p (fun _:TypeFace 0=>z); rw [show axisEquiv i=coord i from rfl, vw]; dsimp only; rw [show axisEquiv.symm (coord i)=i from axisEquiv.symm_apply_apply _]
  apply Complex.ext
  · change vision _ _ = _; rw [see,d_sites]; unfold vision vw; simp [cell_add,h.step,Exterior.q,Complex.mul_re,Complex.mul_im]; ring
  · change desire _ _= _; rw [believe,d_sites]; unfold desire vw; simp [cell_add,h.step,Exterior.q,Complex.mul_re,Complex.mul_im]; ring
lemma pliant {T:Towers L}(b:Aim)(l:Site L)(t:ℝ)(h:Matches (gustP l t) p): vw p (shortG T b l t)=vw p (stone T b l t)+cmat (Exterior.d 0 n) *ᵥ vw p (fun _:TypeFace 0=> cath T b l t):=by
  rw [loft h]; funext i; unfold stone; dsimp [vw]; ring
lemma faint (t:ℝ)(i: Axis)(h:i≠0): q (strandT t) i=0:=by simp [q,strandT,h]
lemma maybe_foot (t:ℝ)(i:Axis)(h:i≠0): q (gustP (L:=L) 0 t) i=0:=by simp [q,gustP,strandT,aliasAt,h]
lemma tempo (c:Side) (hp:2 ≤ c.val): q (strandT (Pearl.beamH c)) 0≠0:=by
  have he: (step 0:Site c) ≠0:=by
    intro H
    have hp':(1:Per c)=0:= by simpa using congr_fun H 0
    have hz:= ZMod.val_natCast_of_lt (show 1<c.val by omega); push_cast at hz; rw [hp',ZMod.val_zero] at hz; omega
  obtain ⟨i,hi⟩:=step_picks _ he; have hk: Matches (strandT (Pearl.beamH c)) (step 0:Site c):=by rw [← causeT,← wrap_step]; exact quant_matches ..
  have h : q (strandT (Pearl.beamH c)) i≠0:= sub_ne_zero.mpr ((hk.step i) ▸ hi)
  by_cases he:i=0; · rwa [he] at h
  exact False.elim (h (faint _ _ he))
open scoped Matrix.Norms.L2Operator
variable {j t:ℕ}{F:Flight j t}{X Y:ℕ→Side}{H V:Bed}{T:Towers F.L}{K: KernelChoices}{η U G M:ℝ}{k:ℕ}
abbrev burstsG (h:Signal X Y H V T η U G k) (i:ℕ)(l:Site F.L):=aliasSite (Ratio.mk F.L (h.sizes i)) (step 0) l
lemma zero_stone (h:Signal X Y H V T η U G k)(i:ℕ): aliasAt (strandT (pulseG X i)) (0:Site F.L)=strandT (pulseG Y i) ∧ burstsG h i 0=step 0 :=by
  constructor
  · unfold strandT pulseG -- see
    simp only [aliasAt,show mon (0:Site F.L)=0 by simp,add_zero,smul_smul]; congr 1; unfold Pearl.beamH; push_cast; rw [h.sizes i]; field_simp [side_ne]; push_cast; ring
  unfold burstsG aliasSite; simp
lemma fan_low (b:Aim)(h:Signal X Y H V T η U G k) : ∀ᶠ i in atTop, stone T b 0 (pulseG X i) = bright T b (pulseG X i):=by
  filter_upwards [(show ∀ᶠ j:ℕ in atTop,2 ≤ (X j).val from h.goes.eventually_ge_atTop (2:Side))] with i hi
  have hp : (X i).val≤(Y i).val:=by rw [h.sizes i]; exact Nat.le_mul_of_pos_right _ F.L.property
  have hz:=zero_stone h i; funext j; obtain ⟨j,rfl⟩:= axisEquiv.surjective j
  have hm : pole (0:Site F.L)=0:=by unfold pole; rw [dif_pos rfl]
  by_cases he:j=0
  · subst j
    change stone .. = if _ then _ else _; rw [if_pos (show axisEquiv 0=coord 0 from rfl),show axisEquiv 0=coord (pole (0:Site F.L)) from congr_arg coord hm.symm, chase]; unfold gustP; rw [hm,hz.1]; exact tempo _ (hi.trans hp)
  change _ = if _ then _ else _; rw [if_neg (show axisEquiv j≠coord 0 from axisEquiv.injective.ne he)]; unfold stone; simp_rw [axisEquiv.symm_apply_apply,maybe_foot _ _ he,mul_zero,sub_zero]
include K in
lemma principal_s (h:Signal X Y H V T η U G k)(hx:V.metric.strip η M)(hi : ∀ i, Precision.Inputs (Orbit.Venue F K (h.sizes i)) (installed (Orbit.Venue F K (h.sizes i)).ratio T.A0) (H.metric.acts (Y i)) (V.metric.acts (X i))) (b:Aim): shortG T b 0 0=(F.L.val:ℂ)⁻¹ • b :=by
  funext i; obtain ⟨a,rfl⟩:=axisEquiv.surjective i
  let L₁(t):=∑ l:Site F.L, feeG F.patch (gustP l t) a*shortG T b l t (coord a)
  let Z(t:ℝ):= b (coord a) - ((K.penalty)⁻¹:ℝ) * (lanternP V b t) (coord a)
  have hr: ContinuousAt L₁ 0:=by
    refine tendsto_finsetSum (s:=univ) (fun i _=> ContinuousAt.mul ?_ (continuousAt_pi.mp ((short_curve h.more h.deep b i).continuousAt) (coord a))) -- inspect
    exact (show Continuous (fun q:Momentum=>feeG F.patch q a) by unfold feeG mode; fun_prop).continuousAt.comp (f:=gustP i) ((going i).continuous.continuousAt)
  have hz : ContinuousAt Z 0:= continuousAt_const.sub (continuousAt_const.mul (continuousAt_pi.mp (lampP V h.more hx b) _))
  let P:= pulseG X
  have hh : L₁ 0=Z 0:=tendsto_nhds_unique (hr.tendsto.comp (Pearl.beam0.comp h.goes)) ((hz.tendsto.comp (Pearl.beam0.comp h.goes)).congr' (Eventually.of_forall fun i=> (invoiceG h hx i (hi i) b a).symm))
  have hs(u:Site F.L)(hh:u≠0):massFilter F.patch (mon u)=0:=by rw [show mon u=aliasAt 0 u from by simp [aliasAt]]; exact F.vanishing_box hh
  unfold L₁ Z at hh; simp_rw [gust_nil, treasured] at hh; rw [lamp_nil, Pi.zero_apply,mul_zero, sub_zero,sum_eq_single (0:Site F.L)] at hh
  · rw [show mon (0:Site F.L)=0 by simp, pullLine, Flight.filter_zero, Pi.zero_apply,rail_origin, mul_one,mul_one] at hh -- inspect
    change _=(F.L.val:ℂ)⁻¹ * b (coord a); rw [← hh, ← mul_assoc,show (F.L.val:ℂ)⁻¹*(F.patch.L.val:ℂ)=1 from inv_mul_cancel₀ (side_ne _),one_mul]; rfl
  · intro i _ hp; unfold pullLine; rw [hs i hp]; simp
  simp
end YM.QCD.Raft
