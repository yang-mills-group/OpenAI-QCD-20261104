import YM.QCD.Reef.Pony
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Fork
variable {D E:Type*} [Fintype D][Fintype E][DecidableEq D][DecidableEq E]{A B:ℝ}
lemma skirtR (R0:Grid f) (X:Grid f→ArrayL D E)(u:D→ Site f)(v:E→Site f)(ht: Heritage u v A 1 j X B)(hz:0<A)(Q:ℝ)(he:0 ≤ Q)(h:∀ (S:Support f) , ∀ x ∈ S,∀ y∈ S, costS m x y ≤ Q*Run.rent 1 j S): Ton u v m (Q*B) (X R0):=by
    obtain ⟨P,R,H⟩:=ht; have hp(i j'): costS m (u i) (v j')* ‖cell (X R0) i j'‖ ≤ Q*duel R i j' 1 j:=by
        rw [← H.sells]; unfold duel; apply le_trans (mul_le_mul_of_nonneg_left (norm_sum_le ..) (cost_nn ..)); rw [mul_sum,mul_sum]; apply sum_le_sum; intro S _;
        have ht:=H.crop i j' S; have hp := ht.2.2.2.1 _ (Run.citizenship f hz R0); rw [← mul_assoc]; by_cases hk:R i j' S=0; · rw [hk] at hp; rw [hk,norm_eq_zero.mpr (norm_le_zero_iff.mp hp)]; simp
        exact mul_le_mul (h S _ (ht.2.1 hk).1 _ (ht.2.1 hk).2) hp (norm_nonneg _) (mul_nonneg he (Real.exp_pos _).le)
    constructor
    · intro i; unfold Gan; apply le_trans _ (mul_le_mul_of_nonneg_left (H.spends i) he); rw [mul_sum]; apply sum_le_sum; intro x _; exact hp ..
    intro i; unfold Gan; apply le_trans _ (mul_le_mul_of_nonneg_left (H.dues i) he); rw [mul_sum]; apply sum_le_sum; intro j _; rw [cell_flip,norm_star,cost_symm]; exact hp ..
open Raft
variable {Ω:ParcelR} {η t σ q:ℝ}
lemma veil (P:Plan j)(Ω:ParcelR)(he:Ω.Rates η)(q:ℝ)(hh:0<σ)(hv:σ≤1) : ∃ Z:ℝ,∀ v:Train j,∀ c:Side,∀ V:Raft.ParcelR.SunR Ω,∀ (u:ℝ),|u|≤q→∀ X:Grid c, Beam ((Fount.FieldB Ω V c σ P v + u • 1) X) 0 Z:=by -- rename
   obtain ⟨K,r,R,hR,hk,hP⟩:= Loom.banner P 1 zero_le_one;
   obtain ⟨δ,T,n,hx,ht,hH⟩:= vaultP he.hr he.hs (show (0:ℝ) ≤1 from zero_le_one) Ω.d Ω.c; obtain ⟨x0,h0,H0⟩:=meal_cost K 0; obtain ⟨x1,h1,H1⟩:=meal_cost n 0
   refine ⟨x0*R+x1*(T*(σ+q)),fun v c V u hu X=>?_⟩; have he:= hH V.X V.Y c n le_rfl σ u hh hv
   have hw:(Fount.FieldB Ω V c σ P v + u • 1) X= wood P 0 v X+trunkM V.X V.Y σ u c X:=by unfold Fount.FieldB trunkM; simp only [Pi.add_apply,Pi.smul_apply]; abel
   rw [hw]; exact (skirtR X _ id id (hP c v) hR x0 h0 (H0 c)).add ((skirtR X _ id id he (mul_pos hx (pow_pos hh _)) x1 h1 (H1 c)).up (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_right hu _) ht.le) h1))
noncomputable def bPeak (x:ℝ)(N:ℕ):ℝ:= (Fintype.card Fiber* (N:ℝ))*((Fintype.card Fiber:ℝ)*N*x)
lemma engineR (N:ℕ)(X:Sheet f)(hp:Beam X 0 t): ‖paleF N X‖ ≤ Fintype.card (Site f)*bPeak t N:=by
   let A:= Modes f N; let p:=copies N X; let K:ℝ:= (Fintype.card Fiber:ℝ)*N
   have h (i:A): ∑ j,‖p i j‖ ≤ K*t:=by
       apply le_trans (b:=∑ j:A,‖cell X i.1.1 j.1.1‖) (sum_le_sum fun j _=> ?_)
       · unfold A Modes Row; rw [Fintype.sum_prod_type]; simp only [Fintype.sum_prod_type,sum_const,card_univ,nsmul_eq_mul]; apply le_trans _ (mul_le_mul_of_nonneg_left (hp.toR i.1.1) (show 0≤ K from by unfold K; positivity)); apply le_of_eq; unfold Gan K; rw [mul_sum]; simp only [costS,pow_zero,one_mul,Flavor,Fintype.card_fin,id]; simp only [mul_assoc]
       change ‖(if i.2=j.2 then X i.1 j.1 else 0)‖ ≤ _; split
       · exact Cost.north (cell X i.1.1 j.1.1) i.1.2 j.1.2
       rw [norm_zero]; exact norm_nonneg _
   change ‖form p‖ ≤ _; unfold form; apply (norm_sum_le ..).trans; apply (sum_le_sum (g:=fun (_:A)=>K*t) ?_).trans (le_of_eq ?_)
   · intro i _; refine (norm_sum_le _ _).trans ((sum_le_sum ?_).trans (h i)); intro j _; rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) ((norm_mul_le ..).trans (by simp only [psi,bar,norm_atom,one_mul,le_rfl]))
   rw [sum_const,card_univ,nsmul_eq_mul]; unfold A Modes Row Flavor K bPeak; simp only [Fintype.card_prod,Fintype.card_fin]; push_cast; ring
lemma cache (hh:1 ≤ t): ‖songT (c:=f) (N:=N) t⁻¹‖≤1:=by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; have hr:0<t⁻¹:=inv_pos.mpr (zero_lt_one.trans_le hh); have he:t⁻¹≤1:=(inv_anti₀ zero_lt_one hh).trans (inv_one.le)
    change ‖engine _ _ x.val‖≤ ‖x.val‖; rw [Grass.norm_def, Grass.norm_def]; apply sum_le_sum; intro j _; rw [fundW,norm_mul,norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le]; exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr.le he)
end YM.QCD.Globe
