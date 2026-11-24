import YM.QCD.RP.Fare

/-!
# Power-of-two torus doubling and a volume-uniform estimate on Grassmann cylinders

Size of tests in l¹ sup. Does not price continuum rescaling, shrinking smears or
multiple insertion renormalization; useful for thermodynamic compactness at fixed spacing.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.RP
open Lattice Wilson Grass Lat NormedSpace Function Finset
open scoped BigOperators Matrix.Norms.Frobenius Matrix Topology
variable {n : Side} {F : ℕ} {C : Lat.Cut n F}

def square (p : Site n) (i : Axis → ℕ) : Set (Site n) := {x|∀ a,(x a-p a).val < i a}
lemma first_scale (h : Even n.val) (hN : 4≤n.val) (hb : 0≤C.β) (hz : 0<C.partitionR)
    (p : Site n) (a : Axis) (i : Axis → ℕ) (hi : 2*i a ≤ n.val) (x : Insertion n F) (H : Floors (square p i) x) (hx : Invariant x) :
    ∃ q y, Floors (square q (Function.update i a (2*i a))) y ∧ Invariant y ∧
      ‖y‖ ≤ ‖x‖^2 ∧ ‖C.average x‖^2 ≤ ‖C.average y‖ := by
  obtain ⟨m,hm⟩ := h
  let R : Cells.Cut n := ⟨⟨m,by omega⟩,by dsimp; omega,.link,a,p a⟩
  let q := Function.update p a (p a - (i a:Per n))
  have ha : square p i ⊆ R.sector := by
    intro x H; have hv := H a
    change (x a - p a).val < m; omega
  let j := Function.update i a (2*i a)
  have hb' : square p i ⊆ square q j := by
    intro u hu s; by_cases e : s=a
    · subst s
      have he := hu a
      simp only [q,j,update_self]
      rw [show u a - (p a - (i a:Per n)) = (( ((u a - p a).val+i a):ℕ ) : Per n) by rw [Nat.cast_add,ZMod.natCast_zmod_val]; abel, ZMod.val_natCast_of_lt (by omega)]; omega
    unfold q j; rw [update_of_ne e,update_of_ne e]; exact hu s
  have hg : Set.MapsTo R.reflect (square p i) (square q j) := by
    intro u hu s
    rcases eq_or_ne s a with he|he
    · subst s; have hx := hu a
      have he : R.reflect u a= 2*p a-1-u a := by simpa only [R,Cells.Kind.shift,Nat.cast_one] using (R.reflect_here u)
      let b := (u a-p a).val
      change b < i a at hx
      simp only [j,q,update_self,he]
      have hv : 2*p a-1-u a-(p a-(i a:Per n))=(( (i a-(b+1)):ℕ):Per n) := by
        have hB : (b:Per n)=u a-p a := ZMod.natCast_zmod_val _
        rw [Nat.cast_sub (by omega),Nat.cast_add,hB]; push_cast; ring
      rw [hv,ZMod.val_natCast_of_lt (by omega)]; omega
    unfold j q; rw [R.reflect_there _ (show s≠R.pos from he),update_of_ne he,update_of_ne he]; exact hu s
  let y := picture R C x*x
  refine ⟨q,y, flooring_mul (pictures H hg) (lower_maps H hb'), invariant_mul _ _ (picture_inv hx) hx,
    (norm_mul_le _ _).trans (by rw [pic_price,pow_two]),?_⟩
  have hr := sch (R:=R) rfl (show 2 ≤ m by omega) hb hz 1 x flooring_one (lower_maps H ha) invariant_one hx
  simpa only [pic_one,one_mul, C.vacuum hz,norm_one] using hr

section doubles
variable (h : Even n.val) (hN : 4≤n.val) (hb : 0≤C.β) (hz : 0<C.partitionR)
include h hN hb hz

lemma reaches (t : ℕ) (p : Site n) (a) (i : Axis → ℕ) (hi : 2^t*i a ≤ n.val)
    (x : Insertion n F) (H : Floors (square p i) x) (hx : Invariant x) :
    ∃ q y, Floors (square q (Function.update i a (2^t*i a))) y ∧ Invariant y ∧
      ‖y‖ ≤ ‖x‖^(2^t:ℕ) ∧ ‖C.average x‖^(2^t:ℕ) ≤ ‖C.average y‖ := by
  induction t with
  | zero => exact ⟨p,x,by simpa using H,hx,by simp,by simp⟩
  | succ t ih =>
    have he : 2^t*i a ≤ n.val := by rw [pow_succ',mul_assoc] at hi; omega
    obtain ⟨q,y,Y,hy,hh,hb⟩ := ih he
    -- hb shadow
    let j := update i a (2^t*i a)
    obtain ⟨s,z,Z,hZ,hk,hw⟩ := first_scale h hN (C:=C) (by assumption) hz q a j (by simpa [j,pow_succ',mul_assoc] using hi) y Y hy
    refine ⟨s,z,?_,hZ,hk.trans ((pow_le_pow_left₀ (norm_nonneg _) hh _).trans (by rw [pow_succ (2:ℕ) t, pow_mul])),?_⟩
    · simpa only [j,update_self,update_idem,pow_succ',mul_assoc] using Z
    rw [pow_succ,pow_mul]; exact le_trans (pow_le_pow_left₀ (by positivity) hb 2) hw

lemma streams {t r : ℕ} (he : 2^t*r=n.val) (p : Site n) (x : Insertion n F)
    (H : Floors (square p fun _ => r) x) (hx : Invariant x) : ∃ y : Insertion n F,
      ‖y‖ ≤ ‖x‖^((2^t)^4:ℕ) ∧ ‖C.average x‖^((2^t)^4:ℕ) ≤ ‖C.average y‖ := by
  let w (s : Finset Axis) (i : Axis) := if i∈s then 2^t*r else r
  have ht (s : Finset Axis) : ∃ (q : Site n) (y : Insertion n F), Floors (square q (w s)) y ∧
      Invariant y ∧ ‖y‖ ≤ ‖x‖^((2^t)^s.card:ℕ) ∧ ‖C.average x‖^((2^t)^s.card:ℕ) ≤ ‖C.average y‖ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨p,x,by simpa [w] using H,hx,by simp,by simp⟩
    | @insert a s h₁ ih =>
      obtain ⟨q,y,Y,hy,hw,HQ⟩ := ih
      have hi : w s a=r := by simp [w,h₁]
      obtain ⟨u,z,Z,hz',he',hg⟩ := reaches h hN hb hz t q a (w s) (by rw [hi,he]) y Y hy
      rw [hi,show update (w s) a (2^t*r)=w (insert a s) from funext fun i => by
        rcases eq_or_ne i a with h|h <;> simp [w,h]] at Z
      rw [card_insert_of_notMem h₁,pow_succ,pow_mul,pow_mul]
      exact ⟨u,z,Z,hz',he'.trans (pow_le_pow_left₀ (by positivity) hw _),le_trans (pow_le_pow_left₀ (by positivity) HQ _) hg⟩
  obtain ⟨_,y,-,-,hw,hx⟩ := ht univ
  exact ⟨y, by simpa [Axis] using hw,by simpa [Axis] using hx⟩
end doubles

lemma growth (p : ℝ) (hp : 0<p) (hc : p^sites n ≤ C.partitionR) (hb : 0≤C.β) (x : Insertion n F) :
    ‖C.average x‖ ≤ ((101+|C.m|)^(12*F)/p)^sites n * ‖x‖ := by
  have hz : 0<C.partitionR := lt_of_lt_of_le (by positivity) hc
  rw [Lat.Cut.average,LinearMap.smul_apply,smul_eq_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hz]
  refine (mul_le_mul_of_nonneg_left (C.test_price hb x) (by positivity)).trans ?_
  rw [← mul_assoc,div_pow]; gcongr; rw [← inv_mul_eq_div]; gcongr

/-- l¹ Grass insertion price from power-one separator. Uses same lattice
quadrature and no continuum compatibility assumption. -/
theorem allows {t r : ℕ} (he : 2^t*r=n.val) (h : Even n.val) (hN : 4≤n.val)
    {b : ℝ} (hB : 0<b) (hp : b^sites n ≤ C.partitionR) (hb : 0≤C.β)
    (p : Site n) (x : Insertion n F) (H : Floors (square p fun _ => r) x) (hx : Invariant x) :
    ‖C.average x‖ ≤ ((101+|C.m|)^(12*F)/b)^(r^4) * ‖x‖ := by
  obtain ⟨y,hy,hz⟩ := streams h hN hb (lt_of_lt_of_le (by positivity) hp) he p x H hx
  apply le_of_pow_le_pow_left₀ (show ((2^t)^4:ℕ) ≠ 0 by positivity) (by positivity)
  apply (hz.trans (growth b hB hp hb y)).trans
  rw [mul_pow, ← pow_mul,show r^4*(2^t)^4 = sites n by
    rw [← mul_pow,mul_comm r,he,sites,site_card]]
  gcongr
end YM.QCD.RP
