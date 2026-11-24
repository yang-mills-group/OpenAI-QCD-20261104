import YM.QCD.Pearl.Wing

/-! # transfer coordinates and Hilliard trace -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Pearl
open Lattice Function Finset Metric Lat Rudder Kit RG Laurent Bloch Flume Free
open scoped Matrix Matrix.Norms.L2Operator BigOperators Kronecker Topology
variable {n : Side} (C : su.Color) {p k : Site n} {P L : Momentum}

def wane (k:Momentum)(p:Walk):Bundle:= mode k (stop 0 p) • 1
def boom (G:Gleam)(k:Momentum):=wane k G.w*wave G.B
def boom₁ (G:Gleam)(a:Axis)(p k:Momentum):= (glitter G.w p a • touch (echo C))*boom G k
def boom₂ (G:Gleam)(a:Axis)(p k:Momentum):= ((glitter G.w (-p) a*glitter G.w p a) • touch (echo C*echo C))*boom G k
def nil₁ (W:Bloom 1)(a:Axis)(p k:Momentum):= (hack (W.petals 0) p a • bloomC C W)*wane k W.tail
def yet₁ (W:Bloom 1)(a:Axis)(p k:Momentum):= ((hack (W.petals 0) p a*glitter W.tail (-p) a+hack (W.petals 0) (-p) a*glitter W.tail p a) • (bloomC C W*touch (echo C)))*wane k W.tail
def yet₂ (W:Bloom 2)(a:Axis)(p k:Momentum):= ((hack (W.petals 0) p a*hack (W.petals 1) (-p) a+hack (W.petals 0) (-p) a*hack (W.petals 1) p a) • bloomC C W)*wane k W.tail

def Fans (p : Site n)(P:Momentum): Prop:=∀ x:Cover,mode P x=cell p (wrap n x)
lemma fanN (p : Site n): Fans p (mon p):= fun _=> (cell_wrap ..).symm
lemma Fans.negative (h: Fans p P): Fans (-p) (-P):=by intro x; rw [mode_inverse,h x,cell_duality (-p),cell_inverse,cell_duality]
lemma Fans.tuned (h : Fans p P)(a : Axis)(w : Walk):glitter w P a=glitter w (mon p) a:=by
  unfold glitter; rw [show flash P a = flash (mon p) a from ?_]
  funext i; unfold flash; split; · rw [h, fanN p _]
  rfl
lemma fan_cell (p x : Site n): cell (-p) x=(cell p x)⁻¹:=by rw [cell_duality,cell_inverse,cell_duality]
lemma boom_P (G:Gleam)(a:Axis)(h:Fans p P) : peel (dew (flashT p a) (silo C 0 G) 0)=cloud p fun k=> boom₁ C G a P (tuning k):=by
  unfold silo; rw [dew_mul_const' (hooked C _ _),mirrorAm, peel_mul, peel_mul, cloudy, unroll 0 _ p, peel_spin]; rw [cloud_side,cloud_side]; congr 1; funext i; dsimp only [boom₁,boom, wane, Pi.mul_apply]; rw [Fans.tuned h,mul_assoc]
lemma boom_Q (G:Gleam)(a:Axis)(h:Fans p P) : peel (dig (flashT p a) (flashT (-p) a) (silo C 0 G) 0)=lined fun k=> boom₂ C G a P (tuning k):=by
  have he (w:Walk): glitter w (-P) a=glitter w (-mon p) a:= (Fans.tuned h.negative ..).trans (Fans.tuned (fanN p).negative a w|>.symm)
  unfold silo; rw [dig_mul_const' (hooked C _ _),bodyAm,peel_mul,peel_mul,line_clear,unroll 0 _ p,peel_spin,lined_law,lined_law]; congr 1; funext i; simp only [Pi.mul_apply,boom₂,boom,wane,he]; rw [mul_assoc,Fans.tuned h a]
lemma law_P (W:Bloom 1)(a:Axis)(h:Fans p P): peel (dew (flashT p a) (silt C 0 W) 0)= cloud p fun k=> nil₁ C W a P (tuning k):=by
  rw [silt_dew]; unfold upL; rw [peel_mul]; simp_rw [rosen h a, ← smul_smul]; rw [cloudy, unroll 0 _ p,cloud_side]; rfl
lemma lawn (X : Weather n) (w:Walk)(v : Site n→Bundle)(Y:Bundle):
    rides (Equiv.refl _) v * pump X w Y=rides (Equiv.refl _) fun i=> bill X i w • (v i*Y):=by rw [pump,ride_mul]; congr 1; funext i; rw [Matrix.mul_smul]; rfl
lemma chal {A : Type*}[AddCommGroup A] [Module ℂ A](v:A)(x y c:ℂ)(hc:c≠0) : (c*x) • ((c⁻¹*y) • v)=(y*x) • v ∧ (c⁻¹*x) • ((c*y) • v)=(y*x) • v:=by rw [smul_smul,smul_smul,mul_mul_mul_comm,mul_mul_mul_comm c⁻¹, mul_inv_cancel₀ hc,inv_mul_cancel₀ hc]; simp [mul_comm]
lemma leaf_Q (W:Bloom 1)(a:Axis)(h:Fans p P): peel (dig (flashT p a) (flashT (-p) a) (silt C 0 W) 0)=lined fun k=> yet₁ C W a P (tuning k):=by
  rw [hewn]; unfold upL; rw [lawn,lawn,ride_add];
  let V:= bloomC C W*touch (echo C); let A:= hack (W.petals 0) P a; let B:=hack (W.petals 0) (-P) a; let U:= glitter W.tail P a; let T:= glitter W.tail (-P) a
  rw [show (fun i : Site n=> bill (flashT (-p) a) i W.tail • _)+(fun i:Site n=> bill (flashT p a) i W.tail • _)= fun i:Site n=> (A*T+B*U) • V from ?_,peel_mul,line_clear,unroll 0 _ p,lined_law]; rfl
  funext i; dsimp only [Pi.add_apply]; rw [billow h a,billow h.negative a, rosen h,rosen h.negative, fan_cell p i, Matrix.smul_mul,Matrix.smul_mul]; rw [add_smul]; congr 1
  · exact (chal V T A (cell p i) (cell_ne p i)).2
  exact (chal V U B (cell p i) (cell_ne p i)).1
lemma sky_Q (W:Bloom 2)(a:Axis)(h:Fans p P): peel (dig (flashT p a) (flashT (-p) a) (silt C 0 W) 0)=lined fun k=> yet₂ C W a P (tuning k):=by
  rw [royal]; simp_rw [jewels,rosen h, rosen h.negative, fan_cell]; simp_rw [mul_mul_mul_comm (cell p _),mul_mul_mul_comm ((cell p _)⁻¹),mul_inv_cancel₀ (cell_ne p _),inv_mul_cancel₀ (cell_ne p _),one_mul]; rw [peel_mul,line_clear,unroll 0 _ p,lined_law]; rfl
end YM.QCD.Pearl
