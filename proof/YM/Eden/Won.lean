import YM.Eden.Yurt
/-! # physical vs untransported Hue. -/
set_option autoImplicit false
noncomputable section
namespace YM.Eden
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free Bloom Arise Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.Frobenius TensorProduct Classical
variable {G:Gauge}{d k i m j:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Bloom Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.PrismD Poised Papyrus Lining Next.Rank.Normal Cylinder
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek Next.Fluctuations
-- signature, x. width bound. proof dependent tiny afterL η. use generic R.
variable (W:Walk)(x:Cover)(U:Grid n)(p:PlaqAxes) (q:Bool)(i j:Dike)
noncomputable def nob (G:Gauge)(s:ℝ)(U:Wilson.Config G n) : Prop:= ∀ e,G.chord (U e) ≤ s
lemma merit(E:Directions su n) {s:ℝ}(F:ℝ)(hz:∀ i:su.Color,‖i‖≤ s → su.chord (su.lieExp i)≤ F*‖i‖)(he:‖E‖≤ s)(hF:0 ≤ F) : nob su (F*s) (increment 1 E):=fun i=>by change su.chord (su.lieExp (E i)*1) ≤ _; have ht:‖E i‖ ≤ s:= (norm_le_pi_norm ..).trans he; rw [mul_one]; exact (hz _ ht).trans (mul_le_mul_of_nonneg_left ht hF)
lemma capC {F:ℝ}(h:nob su F U): ‖su.curvature (faceValue U (slotFace ⟨W,p⟩ (wrap n x)))‖ ≤ 4*F:=by
      refine (su.curvature_norm _).trans ((travel_chord U (Lattice.square p.val.1 p.val.2) _ F h).trans_eq (?_)); norm_num [Lattice.square]
noncomputable def uniR (G:Gauge)(V:Config G n)(x:Cover)(p:Tube G d):ℝ:= hears (fun w:Walk=> (G.curvature (faceValue V (slotFace ⟨w,p.1.2.1⟩ (wrap n x)))) p.2) (rayP p)
noncomputable def style (w:Walk):ℝ:=2*su.colorScale*w.length * 4
lemma stampFee {F:ℝ}(h:nob su F U)(hF:0≤ F):
    ‖RG.Slot.eval ⟨W,p⟩ (expandAt (wrap n x) U) - su.curvature (faceValue U (slotFace ⟨W,p⟩ (wrap n x)))‖ ≤ style W*F^2:=by
      let J:RG.Slot:=⟨W,p⟩; let w:= Lattice.travel U (wrap n x) W; change ‖J.atSite U _- _‖ ≤ _; rw [atSite_path];
      apply (adjoint_norm_sub w _).trans; apply le_trans (mul_le_mul (mul_le_mul_of_nonneg_left (travel_chord U W _ F h) (mul_nonneg (by norm_num) su.colorScale_pos.le)) (capC W x U p h) (norm_nonneg _) (by positivity [su.colorScale_pos])); unfold style; exact le_of_eq (by ring)
lemma ray_bound (i:Tube su d):∃ C:ℝ, 0≤ C ∧∀ {n:Side}(v: Cover)(U:Grid n){F:ℝ},nob su F U → 0 ≤ F → ‖uniR su U v i‖≤ C*F ∧ ‖Bach su d (expandAt (wrap n v) U) i - uniR su U v i‖≤ C*F^2:=by
      let V:=rayP i; let a(w:Walk):=‖V w‖; let J:=V.support; let X:=∑ w∈ J,a w*4; let Y:=∑ w∈J,a w*style w; have h:0 ≤ X:=sum_nonneg fun _ _=> mul_nonneg (norm_nonneg _) (by norm_num); refine ⟨max X Y,h.trans (le_max_left ..),fun {n} v U {F} hv hp=> ?_⟩; let P:=i.1.2.1; constructor
      · apply le_trans _ (mul_le_mul_of_nonneg_right (show X ≤ max X Y from le_max_left ..) hp); unfold uniR hears X; rw[Finsupp.linearCombination_apply,Finsupp.sum,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum (fun j hj=>?_)); rw[norm_smul,mul_assoc]; exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le ..).trans (capC j v U P hv)) (norm_nonneg _)
      apply le_trans _ (mul_le_mul_of_nonneg_right (show Y ≤ max X Y from le_max_right ..) (sq_nonneg _)); let W(i:Walk):= RG.Slot.eval (G:=su) ⟨i,P⟩ (expandAt (wrap n v) U); let Z(i':Walk):= EuclideanSpace.proj (𝕜:=ℝ) i.2 (W i'); rw [show Bach su d (expandAt (wrap n v) U) i= hears Z V from mixH V (EuclideanSpace.proj _) W]; unfold uniR; change ‖hears Z V-hears _ V‖≤_; unfold Y hears; rw [Finsupp.linearCombination_apply,Finsupp.linearCombination_apply,Finsupp.sum,Finsupp.sum,← Finset.sum_sub_distrib,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun j hj=> ?_); rw [← smul_sub,norm_smul, mul_assoc]; exact mul_le_mul_of_nonneg_left ((PiLp.norm_apply_le (W j-su.curvature _) i.2).trans (stampFee j v U P hv hp)) (norm_nonneg _)
-- spin cost ¬transport.Op(e≤F). ΔM reps.Exact.
noncomputable def trPlate(q:Bool)(i j:Dike): Mat →ₗ[ℝ]ℂ where
    toFun x:=peggle q (blux x) i j
    map_add' x y:=by cases q <;> by_cases h: i.2=j.2 <;> simp [peggle,clutch,copies,blux, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_apply,Lat.touch,h,Ne.symm,mul_add]
    map_smul' t x:=by cases q <;> by_cases h:i.2=j.2 <;> simp [peggle,clutch,copies,blux, Matrix.star_eq_conjTranspose, Matrix.blockDiagonal_apply,h, Ne.symm, Lat.touch, Matrix.one_apply]; all_goals split <;> simp
lemma stage_span {F:ℝ}(hf:nob su F U): su.chord (haloW n x W U)≤ W.length *F:=by unfold haloW; rw [travel_at,map_zero, zero_add]; exact travel_chord U W _ F hf
lemma frobs{X:Type}[NormedAddCommGroup X][NormedSpace ℝ X][FiniteDimensional ℝ X](f:X→ₗ[ℝ]ℂ):∃ C:ℝ,0≤C ∧∀ x y:X, ‖f x-f y‖ ≤ C*‖x-y‖:=by
    let G:= f.toContinuousLinearMap; exact ⟨‖G‖,norm_nonneg _,fun x y=>by rw [← map_sub]; exact G.le_opNorm _⟩
lemma costs_tr : ∃ C:ℝ,0≤ C ∧∀ x y:Mat, ‖trPlate q i j x-trPlate q i j y‖ ≤ C*‖x-y‖:=frobs _
lemma role_fee : ∃ C:ℝ,0 ≤ C ∧∀ {n:Side}(o:Cover)(U:Grid n) (F:ℝ), nob su F U →
    ‖beams q n o W U i-beams q n o W 1 i‖ ≤ C*F:=by
       choose X hx hX using fun j:Dike=>costs_tr q i j; let a(j:Dike):=X j*(su.colorScale*W.length); have hp(i:Dike):0≤ a i:=by apply mul_nonneg (hx i); positivity [su.colorScale_pos]
       refine ⟨∑ i,a i, sum_nonneg fun i _=>hp i, fun {n} o U F h=>?_⟩
       unfold beams; rw[←sum_sub_distrib,sum_mul]; refine (norm_sum_le ..).trans (sum_le_sum fun j hj=>?_); rw [← sub_smul, norm_smul,show ‖lineT q (place (landsE n o W) j)‖=1 from (by cases q; exact Grass.norm_atom ..; exact Grass.norm_atom ..),mul_one]; let B:= haloW n o W U;
       rw [tones o W 1 0 q,tones o W 1 0 q, ←mul_sub, norm_mul, Poised.Pipes.ap_one,one_mul,show haloW n o W 1=1 from (by unfold haloW; exact Pressure.one ..)]
       change ‖trPlate q i j (su.mat B)-trPlate q i j (su.mat 1)‖ ≤_; apply (hX j _ _).trans; rw[su.mat_one]; erw [← chord_dist B]; unfold a; simp only [mul_assoc]; apply mul_le_mul_of_nonneg_left _ (hx j); apply mul_le_mul_of_nonneg_left (stage_span W o U h) su.colorScale_pos.le

end YM.Eden
#print axioms YM.Eden.role_fee
#print axioms YM.Eden.ray_bound
