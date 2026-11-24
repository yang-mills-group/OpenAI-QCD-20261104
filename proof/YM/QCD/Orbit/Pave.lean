import YM.QCD.Orbit.Bone

/-! # virtual-replica laws for Schur -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Orbit
open Lat Lattice Wilson Kit Cost Function Finset Tree RG Metric Filter Pine
open Precision Stationary Eyrie Run Revolve Flume Sparks Quarry YM.Next.Free YM.Further.PhysicalPeriodLimitF933 Macrame
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {c C f F m : Side}{k j N:ℕ}(P:Flight j k) (K:KernelChoices)
  {h : f.val=c.val*P.L.val}{H:F.val=C.val*P.L.val} (B:Plan j)
  (L: Lace (P:=P.patch) h H N)
local notation "v₀" => Venue P K h
local notation "V₀" => Venue P K H

lemma mats_lift (M: LegInk f)(W:LegInk F)(d: Site F→ℂ)(hd:Quaint L.high d)(U:Grid f)(hp : W (L.high.links U)* stream L.high d=stream L.high d*M U):
    shiftH P H B W (L.high.links U)*stream L.high d=stream L.high d* shiftH P h B M U:=by
  have hh:= fits_coins P L hd U
  have he : wood B 0 P.wing (L.high.links U)*stream L.high d=stream L.high d*wood B 0 P.wing U:=by
    obtain ⟨t,c,hT,hCL,h⟩:=Rudder.pays_all B; obtain ⟨I,T,H,Hx⟩:=h P.wing
    have he:= raw (P:=queen ∘ T) (Eyrie.trek H) U _ hd
    have hr {n:Side}(W:Grid n) : dust (queen∘T) n W=wood B 0 P.wing W:=by unfold dust; simp_rw [Function.comp_apply, queen_rides]; exact (Hx ..).tsum_eq
    rw [hr,hr] at he; exact he
  unfold shiftH vaultF; rw [Matrix.add_mul,Matrix.add_mul,Matrix.mul_add,Matrix.mul_add,he,hp, Matrix.mul_assoc _ (tied P H 0 (L.high.links U)), hh.1,← Matrix.mul_assoc _ (stream L.low _),hh.2, Matrix.mul_assoc] -- inspect
lemma panels (M:LegInk f)(W:LegInk F)(d : Site F→ℂ)(hd:Quaint L.high d)(U:Grid f)
    (ht:IsUnit (shiftH P h B M U).det) (hu:IsUnit (shiftH P H B W (L.high.links U)).det) (hp : W (L.high.links U)* stream L.high d=stream L.high d*M U):
    shiftL P H B W (L.high.links U)*stream L.low (d ∘ L.R.embed)=stream L.low (d ∘ L.R.embed)*shiftL P h B M U:=by
  let X:=shiftH P H B W (L.high.links U); let Y:= shiftH P h B M U; have he:=mats_lift P B L M W d hd U hp; let k:= stream L.high d
  have hh : X⁻¹*k=k*Y⁻¹:=by
    have h :=congr_arg (fun A : Rail F f=> X⁻¹*A*Y⁻¹) he; change X⁻¹*(X*k)*Y⁻¹=X⁻¹*(k*Y)*Y⁻¹ at h; rw [← Matrix.mul_assoc X⁻¹ X,Matrix.nonsing_inv_mul X hu,Matrix.one_mul,← Matrix.mul_assoc X⁻¹ k Y,Matrix.mul_assoc _ Y Y⁻¹,Matrix.mul_nonsing_inv Y ht,Matrix.mul_one] at h; exact h.symm
  have hv:= fits_coins P L hd U
  let B':=tied P H 0 (L.high.links U); let A:= tied P h 0 U; let D:= stream L.low (d ∘ L.R.embed)
  change (1-B'*X⁻¹*B'ᴴ)*D=D*(1-A*Y⁻¹*Aᴴ)
  rw [Matrix.sub_mul,Matrix.one_mul,Matrix.mul_sub,Matrix.mul_one,Matrix.mul_assoc (B'*_),show B'ᴴ*D=k*Aᴴ from hv.2]; simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc B' X⁻¹ k, hh, ← Matrix.mul_assoc,show B'*k=D*A from hv.1]

variable {V Z: LegInk f}
lemma mir_ink_sync {X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{Q:X→ Grid f}(hq : Army Q 0)(ho: Q 0=1)(hr: ContDiffAt ℝ ω (castF V) 0) : ContDiffAt ℝ ω (V∘Q) 0:=by
  let A:= content ∘ Q
  have hx:= hq.logL ho
  have ht:= (show Tendsto Q (𝓝 0) (𝓝 1) from ho ▸ hq.cont.tendsto).eventually content_encodes
  have hg : A 0=0:=by unfold A; rw [Function.comp_apply,ho, content_one]
  exact (((hg.symm ▸ hr : ContDiffAt ℝ ω (castF V) (A 0))).comp (f:=A) 0 hx).congr_of_eventuallyEq (ht.mono fun k hk=> congr_arg V hk|>.symm)

lemma neighbo (h:f.val=c.val*P.L.val){X:Type}[NormedAddCommGroup X][NormedSpace ℝ X]{Q:X→Grid f}(hp: Blank V)(he:Army Q 0)(ht:Q 0=1): ∀ᶠ x in 𝓝 0, IsUnit (shiftH P h B V (Q x)).det:=by
  have H : ContinuousAt (fun x=> shiftH P h B V (Q x)) 0:=(ContinuousAt.add ((canopy ..).continuousAt.comp he.cont) ((mir_ink_sync he ht hp.2.2.2.2).continuousAt))
  have hv : IsUnit (vaultF B P h 0 1).det:=ticket_inv ..
  have he: shiftH P h B V (Q 0)= vaultF B P h 0 1:=by unfold shiftH; rw [ht,hp.2.2.2.1,add_zero]
  let D x:= (shiftH P h B V (Q x)).det
  have hx : D 0≠0:= by unfold D; rw [he]; exact isUnit_iff_ne_zero.mp hv
  have hu : ContinuousAt D 0:= (Continuous.matrix_det (A:=fun x:Sheet f=>x) continuous_id).continuousAt.comp H; exact (hu.eventually_ne hx).mono (fun _ hi=> isUnit_iff_ne_zero.mpr hi)

end YM.QCD.Orbit
