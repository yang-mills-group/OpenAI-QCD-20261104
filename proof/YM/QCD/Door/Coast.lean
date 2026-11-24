import YM.QCD.Door.Ginger
/-! # dihedral s packages incl trim. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Sway
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Eyrie Sparks
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{j k:ℕ}{L:Flight j k}{H:f.val=c.val*L.L.val}{F:ℕ}
local notation "S"=> sliceL L H
local notation "A"=> Modes f F
local notation "B"=> Modes c F
variable {G:Grid f→Sheet f}{δ a b c' q:ℝ}{l:ℕ} (P:Sun L c f H δ a b c' q l G)

lemma radS {I V :Type*}[Fintype I][Fintype V][DecidableEq I][DecidableEq V]{g:I→Site f}{h:V→Site f}{S₀:Ratio c f}{U:Therm I S₀ g}{W:Therm V S₀ h}{X:Land f I V}(hh: Held S₀ U W X){u:Strut c}{f: _}{P:Spike}(hx:Warrant (raise S₀ u) f P)(x:Grid _)(i j T):
   X i j T (settled (sky (raise S₀ u) x))= lightP (raise S₀ u) P f (g i)* X (U.shiftP u i) (W.shiftP u j) (raiseS S₀ u T) (settled x)*star (lightP (raise S₀ u) P f (h j)):=by
    rw [hh.kept u f P hx x]; unfold driveD; simp only [Equiv.symm_apply_apply, tips,still]; rw [← mul_assoc,← mul_assoc,(license hx _).2,one_mul,mul_assoc,(license hx _).2,mul_one]

variable {u:Strut c}{d:Site f→ℂ}{p:Spike}
abbrev TrU (s : Ratio c f)(P : Strut c)(d:Site f→ℂ)(p:Spike):= chair s (sun s) P p d
abbrev TrV (s : Ratio c f)(P : Strut c)(d:Site f→ℂ)(p:Spike):=chair s (dot s) P p d

lemma wool (hp: Sacred P)(he:Warrant (raise S u) d p)(i: Support f)(x:Grid f):
   flowY P i (sky (raise S u) x)= TrU S u d p * flowY P (raiseS S u i) x *star (TrU S u d p):=by apply whist; intro v w; unfold TrU chair; rw [cell_ride_right,cell_ride_left]; exact radS hp.hearth he x v w i

lemma closeS (Q: Ratio c f)(u:Strut c)(t:ℕ)(i:Site f) (v:Support f): v∈shortZip i t ↔ raiseS Q u v∈ shortZip (act (raise Q u) i) t := by
  let X:=act (raise Q u)
  have ht : v⊆trunkFt i t ↔ v.image X⊆ trunkFt (X i) t:=by
    have he: trunkFt (X i) t=(trunkFt i t).image X :=by unfold trunkFt; rw [← halo_map X (Push.Local.turn_sep _ _)]; simp -- unfolds timing
    rw [he]; exact ⟨image_subset_image,fun H=> image_subset_image_iff X.injective|>.mp H⟩ -- signature
  simp only [shortZip, mem_filter,mem_univ,true_and]; rw [show raiseS Q u v=v.image X from Finset.map_eq_image ..]; exact ht
lemma whittled (Q:Ratio c f)(u:Strut c)(t: ℕ)(i:Site f)(v:Support f): v ∈ satZip i t ↔ raiseS Q u v∈satZip (act (raise Q u) i) t:= by
  constructor
  · intro h; exact Finset.mem_sdiff.mpr ⟨mem_univ _,fun hh=> (Finset.mem_sdiff.mp h).2 ((closeS Q u t i v).mpr hh)⟩
  intro h; exact Finset.mem_sdiff.mpr ⟨mem_univ _,fun hh=>(Finset.mem_sdiff.mp h).2 ((closeS Q u t i v).mp hh)⟩

lemma lane (b:ℕ) (hp:Sacred P)(he:Warrant (raise S u) d p)(i: Support f)(x:Grid f):
   heads P b i (sky (raise S u) x)=TrU S u d p*heads P b (raiseS S u i) x *star (TrV S u d p) ∧
   tailsF P b i (sky (raise S u) x)=TrV S u d p *tailsF P b (raiseS S u i) x*star (TrU S u d p):=by
    constructor
    · apply whist; intro v w; unfold TrU TrV chair; rw [cell_ride_right,cell_ride_left]; change seatL P _ _ _ _ _=_ * seatL P _ _ _ (act (raise S u) v) (act u w)*star _; unfold seatL; simp only [whittled S u b v i]; split; exact radS hp.hedge he x v w i; simp
    apply whist; intro v w; unfold TrV TrU chair; rw [cell_ride_right,cell_ride_left]; change seatV P b _ _ v w=_ *seatV P _ _ _ (act u v) (act (raise S u) w) *star _; unfold seatV; simp only [whittled S u b w i]; split; exact radS hp.heels he x v w i; simp

lemma hike (St: Ratio c f)(u:Strut c)(b:ℕ)(i:Site f)(F :Support f→Bundle): ∑ k∈shortZip (act (raise St u) i) b,F k=∑ k∈shortZip i b,F (raiseS St u k):=by
   rw [show shortZip _ _=(shortZip i b).image (raiseS St u) from ?_,sum_image (raiseS St u).injective.injOn]; ext k; obtain ⟨i,rfl⟩:=(raiseS St u).surjective k; rw [mem_image]; constructor; exact fun h'=>⟨_, (closeS St u b _ _).mpr h',rfl⟩
   rintro ⟨a,hq,H⟩; rw [(raiseS St u).injective H] at hq; exact (closeS St u b _ _).1 hq
lemma shore (b:ℕ)(hp: Sacred P)(he:Warrant (raise S u) d p)(x:Grid f): rL P b (sky (raise S u) x)= TrU S u d p * rL P b x *star (TrV S u d p)∧ rP P b (sky (raise S u) x)=TrV S u d p *rP P b x *star (TrU S u d p):=by
   constructor
   · apply whist; intro i j; unfold TrU TrV chair; rw [cell_ride_right,cell_ride_left]; change seatS P b _ i j= _ * seatS P _ _ (act (raise S u) i) (act u j)* star _; unfold seatS spoon; rw [Finset.sum_apply,Finset.sum_apply,hike]; simp_rw [Matrix.mul_sum,Matrix.sum_mul]; apply sum_congr rfl; intro v _; exact radS hp.hedge he x i j v
   apply whist; intro i j; unfold TrU TrV chair; rw [cell_ride_right,cell_ride_left]; change seatA P b _ i j= _ *seatA P _ _ (act u i) (act (raise S u) j)* star _; unfold seatA spoon; rw [Finset.sum_apply,Finset.sum_apply,hike]; simp_rw [Matrix.mul_sum,Matrix.sum_mul]; apply sum_congr rfl; intro v _; exact radS hp.heels he x i j v
end YM.QCD.Sway
