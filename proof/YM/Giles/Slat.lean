import YM.Giles.Reeds
/-! Kin receipt estimates with z near 0 growing side. Probe errors. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
variable {u t a D C v e s σ :ℝ}{c:Side}{n l d m r k p q w:ℕ}
local notation "Y★"=> Cray c
local notation "G★"=> Lat.Fields c 6
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Complex (exp I)
-- reference scale
local notation "τ"=>tick c
local notation "λρ"=> helm c
lemma lien : ‖helm c‖= tick c:=by unfold helm; rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_of_nonneg (tick_g c).le]
lemma pointζ_first (x:ℝ): ‖pointζ x-1‖≤ ‖x‖:= Real.norm_exp_I_mul_ofReal_sub_one_le
lemma pointζ_later (x:ℝ): ‖pointζ x-1-I*(x:ℂ)‖ ≤ 2*‖x‖^2:=by
    have hx: ‖I*(x:ℂ)‖= ‖x‖:=by rw[norm_mul,Complex.norm_I,one_mul,Complex.norm_real]
    by_cases hp:‖x‖≤1; · unfold pointζ; apply (Complex.norm_exp_sub_one_sub_id_le (hx.le.trans hp)).trans; rw [hx]; nlinarith
    apply (norm_sub_le ..).trans; rw[hx]; have hL:=pointζ_first x; nlinarith [lt_of_not_ge hp]
lemma degree_t(x:ℝ) : ‖λρ⁻¹ * (pointζ (τ*x)-1)- (x:ℂ)‖ ≤2*τ*‖x‖^2:=by
     let Q:=helm c; have hp: Q≠0:= norm_ne_zero_iff.mp (by rw[lien]; exact (tick_g _).ne'); rw [show Q⁻¹* _ - (x:ℂ) =Q⁻¹ * (pointζ (τ*x)-1-I*((τ*x:ℝ):ℂ)) from (by rw [mul_sub Q⁻¹ _ (I*_), Complex.ofReal_mul,← mul_assoc I, show Q⁻¹ * (I*(τ:ℂ)*(x:ℂ))= _ from inv_mul_cancel_left₀ hp (x:ℂ)]),norm_mul]; rw[norm_inv,lien]; apply (mul_le_mul_of_nonneg_left (pointζ_later _) (inv_nonneg.mpr (tick_g _).le)).trans; rw[norm_mul,Real.norm_of_nonneg (tick_g _).le]; apply le_of_eq; field_simp
variable (a b:Axis) (x y: Site c) (T:Taper)
local notation "Θ"=>sepW 0 x y
local notation "Qm"=> (0:Multi 10)
local notation "N"=> Np T
noncomputable def eCost :=normCost /Real.pi
lemma eC0 : 0 ≤ eCost:= div_nonneg cost_pos Real.pi_pos.le
lemma originX : ballast Qm Qm T x y=Np T x*Np T y:=by simp only[ballast,Nw,profile_0,mul_one]
lemma quest_pay: ‖quest x y-N x*N y‖ ≤ eCost * τ * Θ:=by
    apply (variety x y T).trans; unfold eCost tick; rw[sep0]; let v:ℝ:=max (pdist x:ℝ) (pdist y:ℝ); have he: normCost / Real.pi * (2*Real.pi/(c.val:ℝ)) = (normCost/(c.val:ℝ))*2 :=by field_simp
    rw[he,mul_assoc]; apply mul_le_mul_of_nonneg_left _ (div_nonneg cost_pos (by positivity)); change _≤2*(1+v); linarith [show (pdist x:ℝ) ≤ v from le_max_left .., show (pdist y:ℝ) ≤ v from le_max_right ..]
lemma inkL : ‖indexT a x‖≤ Θ∧‖indexT a y‖≤ Θ:=by
    rw [sep0]; refine ⟨(liftN x a).trans ?_, (liftN y a).trans ?_⟩
    · exact (le_max_left ..).trans (le_add_of_nonneg_left zero_le_one)
    exact (le_max_right ..).trans (le_add_of_nonneg_left zero_le_one)
lemma quest_pow(z:ℝ)(C:ℝ)(hC:0≤ C)(hp:‖z‖≤ C*Θ) :
     ‖λρ⁻¹ * ((quest x y)*pointζ (τ*z)-quest x y)- (z:ℂ)*(N x*N y)‖ ≤ (2*C^2+C*eCost)*τ*Θ^2:=by
    let K:=λρ; let P:=quest x y; let X:=K⁻¹* (pointζ (τ*z)-1)-(z:ℂ); let Y:=P-N x*N y
    have ht: ‖X‖ ≤ 2*τ*C^2 * Θ^2:=by
         apply le_trans (degree_t z); calc
         _ ≤ 2*τ*(C*Θ)^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hp 2) (by positivity[tick_g c])
         _=_:=by ring
    have he: ‖Y‖ ≤ eCost*τ*Θ:=quest_pay x y T; change ‖K⁻¹* (P*pointζ (τ*z)-P)- _‖ ≤ _; rw [show K⁻¹* (P*pointζ (τ*z)-P)- ((z:ℂ)*(N x*N y))= X*P+(z:ℂ)*Y from (by unfold X Y; ring)]; apply (norm_add_le ..).trans; rw[norm_mul X P,norm_mul (z:ℂ),show ‖P‖=1 from questW ..,mul_one,Complex.norm_real]; exact (add_le_add ht (mul_le_mul hp he (norm_nonneg _) (mul_nonneg hC (zero_le_one.trans (arm ..))))).trans_eq (by ring)
noncomputable abbrev costQ (C:ℝ):= 2*C^2+C*eCost
lemma costQ_p (C:ℝ)(h:0≤C):0≤costQ C:=by unfold costQ; positivity[eC0]
noncomputable def mu1(a:Axis)(T:Taper)(x y:Site c):ℂ:= ((indexT a x-indexT a y:ℝ):ℂ)*(Np T x*Np T y)
lemma exact1 : scale_e (fun u v:Site c=> λρ⁻¹ *(seek1 1 a u v-seek1 0 a u v)-mu1 a T u v) (costQ 2*τ) 2:=by
    intro x y; let z:= indexT a x-indexT a y; dsimp only; rw [show seek1 0 a x y= quest x y from (by simp[seek1]),show seek1 1 a x y=quest x y * pointζ (τ*z) from ?_]; swap
    · unfold seek1 gaze; rw[healthy,stack]; simp only[Int.cast_one,one_mul]; unfold z; ring_nf
    exact quest_pow x y T z 2 (by norm_num) ((norm_sub_le ..).trans (by linarith only[(inkL a x y).1,(inkL a x y).2]))
noncomputable def mu2(a:Axis)(T:Taper)(x y:Site c):ℂ:= ((-indexT a x:ℝ):ℂ)*(Np T x*Np T y)
lemma exact2 : scale_e (fun u v: Site c=>λρ⁻¹*(seek2 1 a u v-seek2 0 a u v)-mu2 a T u v) (costQ 1*τ) 2:=by
    intro x y; let X:= -indexT a x; dsimp only; rw [show seek2 0 a x y=quest x y from (by simp[seek2]), show seek2 1 a x y=quest x y * pointζ (τ*X) from ?_]; swap
    · unfold seek2 gaze X; rw[healthy]; simp[mul_comm]
    apply quest_pow _ _ T X 1 (by norm_num); rw [one_mul]; unfold X; rw[norm_neg]; exact (inkL a x y).1
lemma seek2_cap(t:ℤ)(a:Axis): scale_e (c:=c) (seek2 t a) 1 2:=by
    intro x y; unfold seek2; rw[norm_mul,norm_star,gaugeG,questW,one_mul,one_mul]; exact one_le_pow₀ (arm ..)
lemma gentle2(a:Axis): scale_e (c:=c) (seek2 1 a-ballast Qm Qm T) ((1+eCost)*τ) 2:=by
    intro x y; rw [Pi.sub_apply,Pi.sub_apply]; let V:= quest x y; rw[originX]
    have he :‖seek2 1 a x y-V‖ ≤ τ*sepW 0 x y :=by
          unfold seek2; rw [show star _ * _ - V=(star (gaze 1 a x)-1)*V from (by unfold V; ring),norm_mul, show ‖V‖=1 from questW .., mul_one]; unfold gaze; simp only[Int.cast_one,one_mul]; rw [healthy]; apply (pointζ_first _).trans; rw [norm_neg,norm_mul,Real.norm_of_nonneg (tick_g _).le]; exact mul_le_mul_of_nonneg_left (inkL a x y).1 (tick_g _).le
    refine (norm_sub_le_norm_sub_add_norm_sub _ V _).trans ((add_le_add he (quest_pay x y T)).trans ?_)
    calc τ*sepW 0 x y+ eCost*τ*sepW 0 x y=(1+eCost)*τ*sepW 0 x y:= by ring
         _≤ (1+eCost)*τ*sepW 0 x y^2:=mul_le_mul_of_nonneg_left (le_self_pow₀ (arm ..) (by norm_num)) (mul_nonneg (by positivity[eC0]) (tick_g _).le)
noncomputable def monoT (b:Axis): Cray c:= fun i=> if i.2=b then 1 else 0
noncomputable def arcT (a b:Axis):Cray c:= fun i=> if i.2=b then indexT a i.1 else 0
lemma monot (b:Axis):waveZ (c:=c) 0 a b= waveZ 0 a b:=rfl -- drop
lemma era0: waveZ (c:=c) 0 a b=admits (monoT b):=by funext i; unfold waveZ admits monoT; split_ifs<;> simp
lemma dart0 : Dart 0 (fun c=>monoT (c:=c) b):=by
    refine ⟨1,zero_le_one,fun c i=>?_⟩; unfold monoT peg; dsimp only; split <;> simp
lemma dart1:Dart 1 (fun c=>arcT (c:=c) a b):=by
    refine ⟨1,zero_le_one,fun c i=>?_⟩; unfold arcT; dsimp only; split; swap; · rw[norm_zero]; positivity [pin_peg i.1 1]
    rw [one_mul,peg,pow_one]; exact (liftN _ _).trans (le_add_of_nonneg_left zero_le_one)
noncomputable def brim (a b:Axis) (c:Side): VerseL c:= (helm c)⁻¹ • (waveZ 1 a b - waveZ 0 a b)-admits (arcT a b) -- shadow notation c!
lemma brims : Chan 2 (fun c=> ((tick c:ℝ)⁻¹ :ℂ) • brim a b c):=by
     refine ⟨2,by norm_num,fun c i=>?_⟩; let t:=tick c; unfold brim; dsimp only; rw[Pi.smul_apply,Pi.sub_apply,Pi.smul_apply,Pi.sub_apply,norm_smul]; unfold waveZ admits arcT; simp only [gaze_nil]; split_ifs; swap; · simp; positivity[pin_peg i.1 2]
     rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg (tick_g c).le]; unfold gaze; simp only[Int.cast_one,one_mul]; apply (mul_le_mul_of_nonneg_left (degree_t (c:=c) _ ) (inv_pos.mpr (tick_g c)).le).trans; rw [show (tick c)⁻¹ * (2* tick c*‖indexT a i.1‖^2)=2*‖indexT a i.1‖^2 from (by field_simp[(tick_g c).ne'])]; apply mul_le_mul_of_nonneg_left _ (by norm_num); exact pow_le_pow_left₀ (norm_nonneg _) ((liftN ..).trans (le_add_of_nonneg_left zero_le_one)) _
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.brims
#print axioms YM.Massive.Patria.Gall.exact1
#print axioms YM.Massive.Patria.Gall.exact2
#print axioms YM.Massive.Patria.Gall.gentle2
