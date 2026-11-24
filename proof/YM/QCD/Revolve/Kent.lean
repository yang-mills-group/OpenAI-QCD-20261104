import YM.QCD.Revolve.Digs

/-! # both involutions on germs, before programs. -/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 40000
namespace YM.QCD.Revolve
open Lat Function Lattice Wilson Kit Pine Cost Eyrie Quarry Finset Filter Stationary Sparks
open scoped Matrix Matrix.Norms.L2Operator Topology ContDiff BigOperators Classical
variable {n: Side}{t: Signed}{p : Spike}{g: Site n → ℂ}

def MirrorF (A:Grid n → Sheet n): Prop:= ∀ (U:Grid n) (s:Signed) (d:Site n→ℂ) (p:Spike), Glare s 0 0 0 d → Swing s p → A (pull s 0 U)=aura (hues 0 s d p) (A U)
abbrev LegInk (n : Side):= Grid n→ Sheet n
def inverted (A: LegInk n)(s: Signed)(U:Grid n):= aura (star (scaleA s n)) (A (pull s 0 U))
lemma inverse_aura (A:Sheet n){B: Sheet n}(h:B∈unitary _): aura B (aura (star B) A)=A:=by unfold aura; simp only [star_star, ← Matrix.mul_assoc,h.2,one_mul]; rw [Matrix.mul_assoc,h.2,mul_one]
lemma combined (A B C : Sheet n): aura A (aura B C)=aura (A*B) C:=by unfold aura; rw [star_mul]; simp [Matrix.mul_assoc]
lemma warmth (A:LegInk n)(s t : Signed)(d : Site n→ℂ)(P:Spike)(he:Glare s 0 0 0 d)(hp:Swing s P):
    ∀ U, aura (star (hues 0 s d P)) (inverted A t (pull s 0 U))=inverted A (s*t) U:=by
  intro U; unfold inverted; rw [pull_pull, show affine s (0:Site n) 0=0 from by simp [affine], combined,← star_mul, scaleA,← troops]; exact compass_eq (rocked he (gems ..)) (hp.prod (fleetLeft _)) _

def hearth (A: LegInk n)(U:Grid n):=
    ((Fintype.card Signed:ℝ)⁻¹) • ∑ s:Signed,inverted A s U
lemma auraCL (B:Sheet n): ∃ L: Sheet n →L[ℝ] Sheet n, ∀ v,L v=aura B v:=by
  let L: Sheet n →ₗ[ℝ] Sheet n:={toFun:=aura B, map_add':=fun _ _=> aura_add ..,map_smul':=fun a v=>by unfold aura; rw [Matrix.mul_smul,Matrix.smul_mul]; rfl}; exact ⟨L.toContinuousLinearMap,fun _=>rfl⟩
lemma roaring (A:LegInk n):MirrorF (hearth A):=by
  intro U s d P hd hp; let B:= hues 0 s d P
  have he : aura (star B) (hearth A (pull s 0 U))=hearth A U:=by
    obtain ⟨L,H⟩:=auraCL (star B); unfold hearth; rw [← H,map_smul,map_sum]; simp_rw [H, show ∀ t,aura (star B) _= _ from fun t=>warmth A s t d P hd hp U];  refine congr_arg (fun X :Sheet n=> ((Fintype.card Signed:ℝ)⁻¹) • X) ?_; exact Equiv.sum_comp (Equiv.mulLeft s) (fun t=>inverted A t U) -- inspect
  rw [← he, inverse_aura _ (colour_wheel hd hp)]

lemma tonicity (hp: Swing t p)(he:Glare t (0:Site n) 0 0 g)(A : Sheet n):
    aura (hues 0 t g p) (newborn n A)= newborn n (aura (hues 0 t g p) A):=by
  obtain ⟨c,hc,H⟩:=chir_line hp; let B:= hues 0 t g p; let V:=chirality n
  have hz : B*V=(c:ℂ) • (V*B):=by
    have hv : star p*g5=c • (g5*star p) := by have he:=congr_arg (·*star p) H; simpa only [Matrix.mul_assoc,hp.unit.2,mul_one,Matrix.smul_mul] using he
    unfold B V chirality hues onSpin; rw [ride_mul,ride_mul,Equiv.trans_refl,Equiv.refl_trans,ride_smul]; congr 1; funext i; simp only [Equiv.refl_apply, Pi.smul_apply,Matrix.smul_mul,Matrix.mul_smul,wave_mul]; rw [hv, smul_comm]; rw [show wave (c • _)=_ from Matrix.smul_kronecker ..]; rfl -- inspect
  unfold newborn; rw [← aura_ad,combined,combined,hz]; unfold aura; rw [star_smul,Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,smul_smul,mul_comm c,hc,one_smul]
def occult (A:LegInk n):= fun U=> ((2:ℝ)⁻¹) • (A U + newborn n (A U))
def newbornL (n:Side): Sheet n →L[ℝ] Sheet n:=LinearMap.toContinuousLinearMap { toFun:=newborn n,map_add':=fun _ _=>new_add ..,map_smul':=fun c A=>by have he (c:ℝ)(A:Sheet n): c • A=(c:ℂ) • A:=rfl; simp only [RingHom.id_apply,he,new_smul]; simp }
lemma occult_t (A:LegInk n)(x:Grid n): newborn n (occult A x)=occult A x:= by unfold occult; change newbornL n _=_; rw [map_smul,map_add, show newbornL n (newborn n _)=_ from new_id (A x),add_comm]; rfl
lemma fire_m (A:LegInk n)(hp:MirrorF A):MirrorF (occult A):=by
  intro U s d p he ht; obtain ⟨L,H⟩:=auraCL (hues 0 s d p); unfold occult; rw [← H,map_smul,map_add]; simp only [H]; rw [hp U s d p he ht, tonicity ht he]

-- prescribe symmetry germs use actual all period rotor. orientation test germ. `MergePres` wants equiv masks on remaining scalar. 
structure Noble (F:trackG n) : Prop where
 praised (s:Signed): ∀ᶠ x : Link su n in 𝓝 0,F (orderTurn s x)=aura (scaleA s n) (F x)
 chiral : (F =ᶠ[𝓝 0] fun x=> newborn n (F x))
lemma Noble.religious {A:LegInk n}(hp:MirrorF A)(he : ∀ x,A x=newborn n (A x)): Noble (A∘input su n):=by
  refine ⟨fun s=> Eventually.of_forall fun x=>?_,Eventually.of_forall fun x=>he _⟩
  rw [Function.comp_apply,show input su n (orderTurn s x)=pull s 0 (input su n x) from (flip_links s x).symm]; exact hp _ _ _ _ (gems ..) (fleetLeft ..)
end YM.QCD.Revolve
