import YM.Oriole.Nett
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
/-! AP plane variation test. Signed from lift seam. Basis heights.G512. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "T" => SpinMode d
local notation "Ae" => Pairs T
local notation "W"=>CensusA d
open Grass.Ward
variable (H:TaperHol)(r:ℝ)(x y:Site c)(P:Cover)(F:Taper)
local notation "Q"=> Massive.Run.plane
local notation "w" i:arg=> Np F i
local notation "f"=> F.χ
local notation "M"=>c.val
local notation "E"=>Complex.exp
local notation "v"=>TorusPCAC.Stencil.nonnegative
open scoped Real
abbrev normCost :=32+4*Real.pi
lemma cost_pos : 0≤normCost:=by unfold normCost; positivity
lemma look : ‖Q x‖=1:= Complex.norm_exp_I_mul_ofReal _
lemma spark : star (w x)= w x:=by unfold Np; rw [star_mul',Lining.Ferry.ap_star]; simp
lemma tintE : ‖w x‖ ≤1:=by
     have hx:‖ap c (Lattice.lift x)‖=1:=by rcases TorusPCAC.Geometry.signs (n:=c) (Lattice.lift x) with h|h; rw[(show ap c _=1 from h), norm_one]; rw[show ap c _= -1 from h,norm_neg,norm_one]
     unfold Np; rw [norm_mul,hx,mul_one,Complex.norm_real,Real.norm_of_nonneg (F.interval _|>.1)]; exact F.interval _|>.2
noncomputable abbrev sumAt(P:Cover):ℝ:= ∑ i:Axis,(P i:ℝ)
set_option quotPrecheck false
local notation "Γ"=> (π / (↑(c.val):ℝ))
lemma amp (P:Cover) : ap c P*Q (wrap c P)= E (Complex.I*(Γ*sumAt P:ℝ)):=by
     let x:= v (wrap c P); let z:= TorusPCAC.Geometry.quotient c P; have he:P=x+M • z:=(TorusPCAC.Geometry.recover P).symm
     have hz:ap c P= ∏ i:Axis, (-1:ℂ)^(z i):=by change TorusPCAC.thermal c P=_; nth_rw 1 [he]; rw [slide_sign, show TorusPCAC.thermal c x=1 from naked _,one_mul] -- thermal ns check
     have hf: Q (wrap c P)= E (Complex.I*(Γ*sumAt x:ℝ)):=by unfold sumAt x; simp [Run.plane,TorusPCAC.Stencil.nonnegative]
     have hu: Γ*sumAt P = Γ*sumAt x+ π * (sumAt z):=by
          have hbx:sumAt P=sumAt x+M*sumAt z:=by unfold sumAt; nth_rw 1[he]; push_cast; simp_rw [Pi.add_apply,Pi.smul_apply,nsmul_eq_mul,Int.cast_add,Int.cast_mul,sum_add_distrib]; congr 1; rw [Finset.mul_sum]; exact sum_congr rfl fun i _=>by push_cast; rfl
          rw [hbx]; field_simp
     have h(K:ℤ) : E (Complex.I*((π * K:ℝ):ℂ))=(-1:ℂ)^K:=by
          rw [show Complex.I*((π * K:ℝ):ℂ)=(K:ℂ)*((π:ℂ)*Complex.I) from by push_cast; ring]; rw [Complex.exp_int_mul,Complex.exp_pi_mul_I]
     rw [hu,hf,hz,Complex.ofReal_add,mul_add,Complex.exp_add, mul_comm]
     apply congr_arg; unfold sumAt; rw [Finset.mul_sum,Complex.ofReal_sum,Finset.mul_sum, Complex.exp_sum]; exact (prod_congr rfl fun i _=> (h (z i)).symm) -- symmetry
lemma liftN (i:Axis): ‖(Lattice.lift x i:ℝ)‖≤ (pdist x:ℝ):=by
      rw[show ‖(Lattice.lift x i:ℝ)‖=( (Lattice.lift x i).natAbs :ℝ) from ?_]; exact_mod_cast Lattice.component_le x i
      rw [Real.norm_eq_abs, ←Int.cast_abs, ← Int.natCast_natAbs,Int.cast_natCast]
-- cost includes taper difference itself
lemma alt : ‖Q x - w x‖ ≤ normCost * (pdist x / (M:ℝ)):=by
     let χ:= F.χ ((M:ℝ)⁻¹ • vector (Lattice.lift x)); have ht: χ ∈ Set.Icc 0 1:= F.interval _; have hm:0 < (M:ℝ):= by exact_mod_cast c.property
     let p':= Lattice.lift x; have hx: ap c p'=1 ∨ ap c p'= -1:= TorusPCAC.Geometry.signs _; have hy: ap c p'*Q x= E (Complex.I*((Γ * sumAt p':ℝ):ℂ)):=by rw [← amp, wrap_lift]
     have he:‖ap c p'‖=1:=by rcases hx with hx|hx<;> simp [hx];
     have hL: ‖sumAt p'‖≤4*(pdist x):=by apply (norm_sum_le ..).trans; apply (Finset.sum_le_sum (g:=fun _:Axis=>(pdist x:ℝ)) (fun i _=>liftN _ _)).trans; norm_num [Axis]
     let cost:ℝ:=pdist x/(M:ℝ); have hp:0≤cost:=by unfold cost; positivity
     have h1: ‖Q x-ap c p'‖ ≤ 4*π*cost:=by
          rw [← one_mul ‖Q x-_‖, ← he,← norm_mul,mul_sub,hy, show ap c p'*ap c p'=1 from TorusPCAC.Geometry.thermal_norm _]; apply (Real.norm_exp_I_mul_ofReal_sub_one_le).trans; rw [norm_mul,Real.norm_of_nonneg (by positivity :0 ≤π/(M:ℝ))]; exact (mul_le_mul_of_nonneg_left hL (by positivity)).trans (le_of_eq (by unfold cost; ring))
     have h2 : ‖ap c p'-w x‖ ≤ 32*cost:=by
          by_cases hx: cost ≤ 1/8
          · have hχ: χ=1:= by refine F.near _ fun i=>?_ ; change |((M:ℝ)⁻¹)*(p' i:ℝ)|≤_; rw [abs_mul, abs_of_nonneg (by positivity), ←Real.norm_eq_abs]; exact (mul_le_mul_of_nonneg_left (liftN _ _) (by positivity)).trans ((show (M:ℝ)⁻¹*(pdist x)=cost from by unfold cost; ring) |>.le.trans hx) -- meta
            change ‖ap c p'-(χ:ℂ)*_‖ ≤ _; rw [hχ,Complex.ofReal_one,one_mul,sub_self,norm_zero]; positivity
          exact (norm_sub_le _ _).trans (by have hp:= tintE x F; linarith)
     exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans ((add_le_add h1 h2).trans (le_of_eq (by unfold normCost cost; ring))) -- order?
lemma variety: ‖(star (Q x)*Q y-w x*w y)‖ ≤ (normCost/(M:ℝ)) *(pdist x+pdist y:ℝ):=by
     let S:=star (Q x)*Q y; let R:=w x*w y; let H:=(star (Q x-w x))*Q y; let J:=w x*(Q y-w y); have h:S-R=H+J:=by unfold S R H J; simp_rw [star_sub,spark]; ring
     have hL:‖H‖≤ normCost*(pdist x / (M:ℝ)):=by rw [show ‖H‖= ‖Q x-w x‖ from (by unfold H; rw[norm_mul,norm_star, look,mul_one])]; exact alt x F
     have hV:‖J‖≤ normCost*(pdist y/(M:ℝ)):= (norm_mul _ _).le.trans ((mul_le_of_le_one_left (norm_nonneg _) (tintE x F)).trans (alt y F))
     change ‖S-R‖ ≤ _; rw[h]; exact (norm_add_le ..).trans ((add_le_add hL hV).trans (le_of_eq (by ring)))
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.variety
