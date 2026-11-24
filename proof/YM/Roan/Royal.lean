import YM.Roan.Ode
import YM.Roan.Africa
import YM.Roan.Wire
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp.Stair
open Filter Function Set Lattice Wilson RG Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Poised Poised.Beacon Poised.Display Poised.Stative Poised.Sieve
open Finset Tawny Tawny.Cast Tawny.Cast.Rays Tawny.Cast.Carnal Tawny.Cast.TableT Tawny.Pane Tawny.BendR
open Oriole Counting Counting.Click PCAC Patria.Gall.Seals Patria.Gall
-- incomes cost norm.S
local notation "Z"=> RawVec 10
variable (u a α ε L Q A₂ M B C D θ e:ℝ)
variable {n:ℕ}(p:ℕ→Z)(Pt:ℕ→BudgetPoint)(A V:ℕ→ℝ)(W:Axis→ℕ→ℝ)
variable (hP : Pan n p Pt W A V u α a ε)
local notation "Hℓ" z:arg => (L*z)
local notation "F₀"=> (Fintype.card (Rings 10):ℝ)
-- supersed stage.V Costs. Hype L = d^4 or d^5. β budgets polynomial choose later.
local notation "Y" x:arg=> (L*a)
local notation "φ" L:arg=> ((L*F₀)*(α*u^8))
local notation "δ" L:arg=> (L*F₀*(2*ε))
local notation "τ" L:arg=> (B+2*(L*a+1)*M)
local notation "∆e" L:arg=> (δ L * τ L + θ*M)
local notation "ΦL" L:arg n:arg=> (B+n*(∆e L)) -- n real
local notation "ψω" L:arg n:arg=> (φ L*(ΦL L n)+δ L*(τ L))
local notation "Φ" L:arg => δ L * τ L
local notation "Ω" L:arg=> φ L * (Φ L)+ δ L * τ L+ θ*M
set_option quotPrecheck false
local notation "p★" i:arg=> (Pt i).threshold
local notation "co" Lp:arg S:arg j:arg=> compass (cashR Lp S n j) (A j)
local notation "tX" Lp:arg S:arg j:arg=> torque (cashR Lp S n j) (A j)
local notation "po" Lp:arg S:arg j:arg=> point (p★ j) (cashR Lp S n j) (A j)
variable {S t s:ℝ}(l:ℝ) (hX:Signature C D)
local notation "costA"=> D*(C*e)
local notation "costT"=> D*(C*M)
-- define gross endpoint decoded errors
variable (hF:FundX u a α ε (l^4) (l^5) M B θ e n)(hh:3 ≤ l)(hw:l*u^2=1)(hα:4*a*u≤1/2)(hT:Stair.Twist n Pt A V l u θ) (hQ:0 < S)(hZ:∀ j,W j n≤ B*S)
include hF hh hw hα hT hX hQ hZ hP
lemma resumeY : ∀ j:Axis,∀ v:ℕ,v≤ n → W j v ≤ (cashR (l^4) S n v)⁻¹ * (B+(2*((l^4)*a+1))*M):=by
       let L:=l^4; have hl:0<l:=lt_of_lt_of_le (by norm_num) hh; have hL:0<L:=pow_pos hl _; let u':=cashR L S n
       let T:= trunks p Pt A u'; let K(k:Fin 4):=nuP k Pt A V u L
       obtain ⟨he,hx,hz⟩:= cash_κ L S hL hQ n
       have hup:= hP.step; have hd:= motionV a u l hw hP.prim hup hh hα
       have hBB(a:ℝ)(h:a≤B*S):u' n*a ≤B:=by unfold u'; rw[hz,mul_comm,one_div,←div_eq_mul_inv]; exact (div_le_iff₀ hQ).mpr h
       have h (j:Axis) : (∀ i:ℕ,i≤ n → blip T j i≤ M) ∧ wages j (T 0 0 -T n 0) ≤ e:=by
             let Z1:=fun i=>u' i*W j i; have hh₁:= shinesG α a ε L u j hP hL.le he hx hd.1; have hg:Z1 n ≤B:= hBB _ (hZ _); have ht:wages j (T n 0)≤B:= (paso ..).trans ((hh₁.funds n le_rfl).trans hg)
             have hε:=hP.toxin; have ha:=hP.script; have hD:=hF.north; let g:= ΦL L (n:ℝ); let H:=(wages j (T n 0)+n*(∆e L)); have hh:H≤ g:= add_le_add_left ht _; have heA:0 ≤ φ L:= by positivity
             have hp: H+B+3*(n*(φ L*H+δ L*(τ L)))< M:=by
                   refine lt_of_le_of_lt ?_ hD; refine add_le_add (add_le_add_left hh B) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left (mul_le_mul_of_nonneg_left hh heA) _) (Nat.cast_nonneg _)) (by norm_num))
             have hΨ:= strongY j T K Z1 (L*a) (φ L) (δ L) θ B M (mul_nonneg hL.le hP.prim) heA (by positivity) hF.e_ng hh₁ hg hT.x hT.eT hF.m_ng hp
             have heΩ:= hΨ.2 0 (Nat.zero_le n); rw [Nat.sub_zero] at heΩ; exact ⟨hΨ.1, heΩ.trans hF.desire⟩
       intro j v hv
       have h₁:0 ≤L*a:=mul_nonneg hL.le hP.prim; have hh₁:= shinesG α a ε L u j hP hL.le he hx hd.1
       have hφ : u' v* W j v ≤ B+ (2*(L*a+1))*M:= startup _ _ _ _ (L*a) _ _ _ _ h₁ hh₁ (h j).1 (hBB _ (hZ j)) v hv
       rw[le_inv_mul_iff₀ (he _)]; exact hφ
local notation "ΓH" i:arg=> (cashR (l^4) S n i)⁻¹ * (B+(2*((l^4)*a+1))*M)
-- uniform for p records at any interior.S,distance sequence fixed.L.
omit hP hZ hQ hX hF hT hh hα hw
-- Evaluated W raw norm control. pre data.Reusable
set_option maxHeartbeats 800000 in
lemma paidN (b:ℝ)(k:BudgetPoint)(v:ℝ)(ht:0<v)(hb:0 ≤b):∃ C:ℝ,0≤C ∧∀ p:Z,(∀ i:Axis, Plans.wealth (p.val i).val k.threshold v≤b)→‖p‖≤ C:=by
       obtain ⟨C,hp,hK⟩:= scaleK0; -- point via stack and sum
       let p0(i:Fin 4) := bud i k.threshold v -- specify
       let M:= ∑ j:Fin 4,(p0 j)⁻¹ * (C*b); have htU(i:Fin 4):0<p0 i:=mul_pos (pow_pos k.threshold_pos _) (pow_pos ht _); refine ⟨M,sum_nonneg (fun i h=>by positivity [htU i]),fun p hB=>?_⟩
       suffices h:∀ i:Fin 4,‖bet i p‖≤(p0 i)⁻¹*(C*b) by
            nth_rw 1[bill_zero p]; exact (norm_sum_le ..).trans (by unfold M; exact sum_le_sum (fun j _=>h j))
       intro i; have hW:‖stack i k.threshold v p‖≤ C*b:=by
             apply hK _ _ (fun j=>?_)
             exact (single_le_sum (s:=univ) (f:=fun i:Fin 4=> wages j (stack i k.threshold v p)) (fun i _=>wageG ..) (mem_univ i)).trans ((wow p k.threshold v j).ge.trans (hB _)) -- signature
       rw[le_inv_mul_iff₀ (htU i)]; unfold stack at hW; rw [norm_smul,Complex.norm_real,Real.norm_of_nonneg (htU _).le] at hW; exact hW
end YM.Massive.Poised.Plans.Stamp.Stair
#print axioms YM.Massive.Poised.Plans.Stamp.Stair.paidN
