import YM.QCD.Globe.Cumin
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
variable {X: Sheet c}{C W w:ℝ}
lemma humid (p: Site c)(i j:Site c)(x:Sheet c): cell (rake p m x) i j=((separation p j:ℂ)-separation p i)^m • cell x i j:=by
   induction m generalizing x with
   | zero=> simp[rake]
   | succ j ih=>rw [rake,Function.comp_apply,ih, rakeZ,smul_smul,pow_succ]
noncomputable def prair (j:ℕ):ℝ:= (1+(j:ℝ))^(-6:ℤ)
lemma wavesMC :∃ C:ℝ,0≤ C∧∀ c:Side,∀ x:Site c,∑ y:Site c,prair (separation x y)≤ C:=by
    let f(i:ℕ):ℝ:=(1+(i:ℝ))^(-2:ℤ); have hnn : ∀ i,0≤ f i:=fun i=>by unfold f; positivity
    have hf: Summable f:=by
       -- shift sum
       have h:Summable (fun i:ℕ=> (1:ℝ)/(i:ℝ)^ (2:ℕ)):= Real.summable_one_div_nat_pow.mpr (by omega)
       have ht:=h.comp_injective (show Injective (fun i:ℕ=>i+1) from by intro a b h; dsimp only at h; omega)
       apply ht.congr; intro b; unfold Function.comp f; push_cast; rw [show (-2:ℤ)=-((2:ℕ):ℤ) from rfl,zpow_neg,zpow_natCast, add_comm (1:ℝ),one_div]
    refine ⟨16*∑' i,f i, mul_nonneg (by norm_num) (tsum_nonneg hnn),fun c x=>?_⟩; let g(y: Site c):=separation x y; let U:Finset (Site c):=univ; rw [← sum_fiberwise_of_maps_to (s:=U) (g:=g) (t:=U.image g) (by intro a ha; exact mem_image_of_mem _ ha)]; -- need names
    apply le_trans _ (mul_le_mul_of_nonneg_left (hf.sum_le_tsum (U.image g) fun i _=> hnn i) (by norm_num : (0:ℝ)≤16)); rw [mul_sum]; apply sum_le_sum; intro i _; let t:=U.filter fun v=> g v=i
    have hl : t.card ≤ (i+i+1)^4 := (card_le_card (show t⊆ Lattice.halo i {x} from fun a ha=> halo_spec.mpr ⟨x,mem_singleton_self _,(mem_filter.mp ha).2.le⟩)).trans (by simpa using Corona.halo_size ({x} : Support c) i)
    rw [show (∑ p∈t,prair (g p))=∑ _∈t,prair i from sum_congr rfl (fun j hj=>by rw [(mem_filter.mp hj).2]),sum_const,nsmul_eq_mul]; have hu:(t.card:ℝ) ≤ ((2:ℝ)*(i+1:ℝ))^4:=by
           apply le_trans (Nat.cast_le.mpr hl); push_cast; gcongr; linarith
    apply (mul_le_mul_of_nonneg_right hu (by unfold prair; positivity : 0 ≤ prair i)).trans; unfold prair f; apply le_of_eq; push_cast; field_simp; ring
lemma thickV (a b:ℝ)(ha:0≤a)(hb:0≤b):∃ C:ℝ,1≤ C∧∀ (c:Side)(X:Sheet c), Beam X 6 a→ ‖X⁻¹‖≤b→IsUnit X.det → Beam X⁻¹ 0 C:=by
    obtain ⟨K,hK,H⟩:= shack a b ha hb 6; obtain ⟨T,hT,hP⟩:=wavesMC; let C:ℝ:=2^6*K; have hc:0 ≤ C:=by unfold C; positivity
    refine ⟨max 1 (C*T), le_max_left ..,fun c X hp hv hz=>?_⟩; apply Ton.up _ (le_max_right ..); let Y:=X⁻¹
    have hh(x y:Site c):‖cell Y x y‖ ≤ C*prair (separation x y):=by
        let p:=separation x y; by_cases h:p=0
        · rw [show separation x y=0 from h]; unfold prair; simp only [Nat.cast_zero,add_zero,one_zpow, mul_one]; exact (Run.cell_pay ..).trans (show ‖X⁻¹‖≤ C from le_trans (show _≤K from H 0 (by decide) c X hp hv hz x) (le_mul_of_one_le_left hK (by norm_num)))
        have h0:(1:ℝ)≤ p:=Nat.one_le_cast.mpr (by omega); have hA: p^6 * ‖cell Y x y‖ ≤ K := by
             have he:= (Run.cell_pay x y (rake x 6 X⁻¹)).trans (H 6 le_rfl c X hp hv hz x); rw [humid x,separation_self, Nat.cast_zero,sub_zero,norm_smul,norm_pow,show ‖(↑(separation x y):ℂ)‖=(p:ℝ) from ?_] at he; exact he
             simp[p]
        change _ ≤ C*prair p; unfold prair; rw [show (-6:ℤ)= -((6:ℕ):ℤ) from rfl,zpow_neg,zpow_natCast,← div_eq_mul_inv,le_div_iff₀ (by positivity :0 < (1+(p:ℝ))^6)]; apply le_trans (b:= ‖cell Y x y‖*(2*p)^6) (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (show 1+(p:ℝ) ≤2*p by linarith) _) (norm_nonneg _)); rw [mul_pow]; linarith only [hA]
    constructor
    · intro i; apply le_trans _ (mul_le_mul_of_nonneg_left (hP _ i) hc); rw [mul_sum]; refine sum_le_sum fun j _=>?_ ; rw [costS,pow_zero,one_mul]; exact hh ..
    intro i; apply le_trans _ (mul_le_mul_of_nonneg_left (hP _ i) hc); rw [mul_sum]; refine sum_le_sum fun j _=>?_ ; rw [costS,pow_zero,one_mul,cell_flip,norm_star,separation_comm]; exact hh ..
end YM.QCD.Globe
