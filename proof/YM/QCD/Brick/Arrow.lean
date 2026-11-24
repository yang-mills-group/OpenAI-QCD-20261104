import YM.QCD.Brick.Feather
/-! # The lag payment once per bilinear instead of once per leg -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Brick
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent
variable {D:Type*}[Fintype D] {X Y:Cover→Alg D}{w:D→ℕ}{m:ℕ}{x y:Cover}{u v a A p p' z:ℝ}
-- paper normalized K. m = upper cover norm (not B). distinguish order. M* for far.
section
variable (h:Lien w v u A X) (hp: Lien w v u A Y) (hx: size x ≤ m) (hy:size y≤ m) (hu:0<u)(hv:0 ≤v) (hV:v ≤1) (hA:0≤A)
include h hx hv hA
local notation "ρ"=> visc w u
abbrev eBeam (X: Cover→Alg D)(y:Cover):= affineD (fun i=>gust X i 0) y
lemma podium (he: (m:ℝ)*v ≤ 1) : ρ (X x) ≤ A*9 ∧ ρ (X x-X 0) ≤ m*(9*A*v) ∧ ρ (X x-X 0-eBeam X x) ≤ m^2*(9*A*v^2) := by
   have hi : (2+(m:ℝ)*v)^2 ≤9:= (pow_le_pow_left₀ (by positivity) (show 2+m*v ≤ 3 by linarith) 2).trans_eq (by ring)
   refine ⟨(h.poses x m hx).1.trans (mul_le_mul_of_nonneg_left hi hA),?_ ,?_⟩
   · refine (walkQ x m hx X (p:=9*A*v) (fun j x ha _=>?_)).trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (by positivity : 0≤9*A*v)); exact (h.first x m ha j).trans ((mul_le_mul_of_nonneg_left hi (mul_nonneg hA hv)).trans_eq (by ring))
   refine (safari x m hx X (p:=9*A*v^2) (fun i j x ha=>?_) (by positivity)); exact (h.second x m ha i j).trans ((mul_le_mul_of_nonneg_left hi (mul_nonneg hA (sq_nonneg _))).trans_eq (by ring))
omit hx hv hA in
lemma site : ρ (X 0) ≤ 4*A ∧ dryL u (X 0) ≤ A :=by
   have hh:= h.poses 0 0 (by simp [Laurent.size]); exact ⟨hh.1.trans_eq (by push_cast; ring), hh.2⟩ -- omit hx
lemma hear_pr : ρ (eBeam X x) ≤ m*(4*A*v):= le_trans (valAffine _ x (p:=4*A*v) fun i=> (h.first 0 0 (by simp [Laurent.size]) i).trans_eq (by push_cast; ring)) (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hx) (by positivity))
include hp hy hu
abbrev blossom (X Y: Cover→ Alg D)(x y: Cover) := X 0*Y 0+eBeam X x * Y 0 + X 0* eBeam Y y
private def lump {A:Type*}[Ring A](x y a b F G: A):= (x-a-F)*b+(x-a)*(y-b)+a*(y-b-G)
set_option maxHeartbeats 300000 in
lemma stripB (he : m*v ≤ 1) : ρ (X x * Y y-X 0*Y 0) ≤ 340 * A^2*(m*v) ∧ ρ (X x*Y y-blossom X Y x y) ≤ 340*A^2*(m*v)^2 :=by
   let x':= X x; let y':=Y y; let a:= X 0; let b:= Y 0; have hh:=podium h hx hv hA he; have hS:= podium hp hy hv hA he; let δ:=(m:ℝ)*v; have ht:0≤δ:=mul_nonneg (Nat.cast_nonneg _) hv
   have ha:ρ a ≤ A*9:= (podium (x:=(0:Cover)) h (by simp [Laurent.size]) hv hA he).1
   have hb:ρ b ≤ A*9:= (podium (x:=(0:Cover)) hp (by simp [Laurent.size]) hv hA he).1
   have h (b c: Alg D)(z v:ℝ)(hp:ρ b ≤ z)(hx:ρ c ≤ v):ρ (b*c) ≤ z*v:=(roams w hu.le ..).trans (mul_le_mul hp hx (norm_nonneg _) ((norm_nonneg _).trans hp))
   constructor
   · rw [show _ - _* _=(x'-a)*y'+a*(y'-b) from ?_] -- edit
     · apply (vested ..).trans; exact (add_le_add (h _ _ _ _ hh.2.1 hS.1) (h _ _ _ _ ha hS.2.1)).trans (by nlinarith only [mul_nonneg (sq_nonneg A) ht])
     unfold x' y' a b; noncomm_ring
   let F:=eBeam X x; let G:=eBeam Y y
   rw [show x'*y'- blossom X Y x y=lump x' y' a b F G from ?_] -- define abbrev or expand
   swap; · unfold a b F G lump blossom; noncomm_ring
   exact (vested ..).trans ((add_le_add ((vested ..).trans (add_le_add (h _ _ _ _ hh.2.2 hb) (h _ _ _ _ hh.2.1 hS.2.1))) (h _ _ _ _ ha hS.2.2)).trans (by nlinarith only [mul_nonneg (sq_nonneg A) (mul_nonneg (sq_nonneg v) (sq_nonneg (m:ℝ)))])) -- orderA
include hV
lemma flying (he :1≤ m*v) : ρ (X x * Y y-X 0*Y 0) ≤ 340 * A^2*(m*v)^2 ∧ ρ (X x*Y y-blossom X Y x y) ≤ 340*A^2*(m*v)^2:=by
   let δ:=m*v; have hx₀: 0≤δ:=by positivity
   have hz1:= le_self_pow₀ he (show 2≠0 by norm_num); have hz2:=one_le_pow₀ (n:=2) he; let w':= A*9*δ^2
   have hp₀ : A*(2+δ)^2 ≤ w':=(mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) (show 2+δ≤3*δ by change 1 ≤ δ at he; linarith) 2).trans (le_of_eq (show (3*δ)^2=(9*δ^2:ℝ) by ring))) hA).trans_eq (by unfold w'; ring)
   obtain ⟨hu1,hu2⟩:= h.poses x _ hx; have hg:= hu1.trans hp₀; obtain ⟨hx1,hx2⟩:= hp.poses y _ hy; have hz:= hx1.trans hp₀
   have hQ: ρ (X x*Y y) ≤ w'*A+A*w':=(lightD hu ..).trans (add_le_add (mul_le_mul hg hx2 (load_nn ..) (by unfold w'; positivity)) (mul_le_mul hu2 hz (norm_nonneg _) hA))
   have ha: ρ (X 0) ≤ 4*A:= (site h).1 -- invocation order? inspect implicit
   have hb: ρ (Y 0) ≤ 4*A:= (site hp).1
   have hhP: ρ (X 0*Y 0) ≤ (4*A)*(4*A):=(roams w hu.le ..).trans (mul_le_mul ha hb (norm_nonneg _) (by positivity))
   have hv : 1≤δ^2:=hz2; have hm: ρ (X x*Y y)≤ 18*A^2*δ^2:= hQ.trans_eq (by unfold w'; ring)
   refine ⟨(vertex ..).trans ((add_le_add hm hhP).trans ?_), (vertex ..).trans ?_⟩; · change _ ≤ 340*A^2*δ^2; nlinarith only [mul_le_mul_of_nonneg_left hv (sq_nonneg A)]
   have hf:= (roams w hu.le ..).trans (mul_le_mul (hear_pr h hx (by assumption) hA) hb (norm_nonneg _) (show 0≤ _ by positivity))
   have hc:= (roams w hu.le ..).trans (mul_le_mul ha (hear_pr hp hy (by assumption) hA) (norm_nonneg _) (show 0 ≤ 4*A by positivity))
   apply (add_le_add hm ((vested ..).trans (add_le_add ((vested ..).trans (add_le_add hhP hf)) hc))).trans; unfold δ
   unfold δ at hv; nlinarith only [mul_le_mul_of_nonneg_left hz1 (sq_nonneg A),mul_le_mul_of_nonneg_left hv (sq_nonneg A)]
lemma pollinate : ρ (X x * Y y-X 0*Y 0) ≤ 340*A^2*v*(1+m)^2 ∧ ρ (X x * Y y-blossom X Y x y) ≤ 340*A^2*v^2*(1+m)^2:=by
   have he: 0≤340*A^2:=by positivity
   have hp₀: m*v≤(1+(m:ℝ))^2*v:=mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) m]) hv
   have he₀: 340*A^2*(m*v)^2 ≤340*A^2*v^2*(1+m)^2:=by rw [mul_pow]; calc
     _ = 340*A^2*v^2*m^2:=by ring
     _ ≤ _:=by gcongr; linarith
   cases le_total (m*v) 1 with
   | inl h' => obtain ⟨h1,h2⟩:= stripB h hp hx hy hu hv hA h'; exact ⟨h1.trans ((mul_le_mul_of_nonneg_left hp₀ he).trans_eq (by ring)),h2.trans he₀⟩
   | inr h' => obtain ⟨h1,h2⟩:=flying h hp hx hy hu hv hV hA h'; exact ⟨(h1.trans he₀).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by nlinarith only [hv,hV] : v^2≤v) he) (sq_nonneg _)),h2.trans he₀⟩
end
end YM.QCD.Brick
