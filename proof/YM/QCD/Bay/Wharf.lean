import YM.QCD.Bay.Hour
/-! # Pulse re-pack. An evaluator field with covariance, not using its analytic extension on old supports across varying links. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Bay
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Strut LeafM
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V]{f c: Side}{g:D→ Site f}{h:V→Site f}{δ A t a:ℝ}{m:ℕ}

structure Therm (D:Type*) {f c: Side} (S:Ratio c f)(g:D→Site f) where
 shiftP : Strut c→Equiv.Perm D
 steps (s u) : shiftP (pod s u) = (shiftP u).trans (shiftP s)
 bills (s i): g (shiftP s i)=act (raise S s) (g i)

-- Swept maps actual matrix via rides, g U. len. Crop uses trans. Myths.
variable (s: Ratio c f)(P:Therm D s g) (Q:Therm V s h)

abbrev chair (u:Strut c)(T:Spike)(l: Site f→ℂ) : ArrayL D D := rides (P.shiftP u) fun x=> lightP (raise s u) T l (g x)
structure Tow (G: Grid f→ArrayL D V) : Prop where
 goes (u:Strut c)(l:Site f→ℂ)(T:Spike)(U: Grid f): Warrant (raise s u) l T→ G (sky (raise s u) U)=chair s P u T l *G U *star (chair s Q u T l)
variable {s} {P Q}

lemma cell_ride_left (M: ArrayL D V)(F:D→Bundle)(R : Equiv.Perm D)(i j): cell (rides R F *M) i j= F i* cell M (R i) j:=by
  rw [cell_mul,sum_eq_single (R i)]; · rw [show cell (rides R F) i (R i)=F i from ?_]; ext a b; exact if_pos rfl
  · intro x _ hx; have he :cell (rides R F) i x=0:=by ext a b; exact if_neg (Ne.symm hx); -- semicolon
    rw [he,zero_mul] -- check noncomm
  simp
lemma cell_ride_right (M : ArrayL D V)(F: V→Bundle)(R:Equiv.Perm V)(i j): cell (M*star (rides R F)) i j=cell M i (R j) * star (F j):=by
  have ht : star (cell (rides R F*Mᴴ) j i)= cell (M*star (rides R F)) i j:=by rw [←cell_flip,Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]; rfl
  rw [← ht, cell_ride_left,star_mul, cell_flip,star_star]

lemma stages {F:Grid f→ArrayL D V}(K: Tow s P Q F)(u:Strut c)(U: Grid f)(l:Site f→ℂ)(T:Spike)(hv:Warrant (raise s u) l T)(i j): cell (F (sky (raise s u) U)) i j=lightP (raise s u) T l (g i)* cell (F U) (P.shiftP u i) (Q.shiftP u j)*star (lightP (raise s u) T l (h j)):=by rw [K.goes u l T U hv]; unfold chair; rw [cell_ride_right,cell_ride_left]

variable (s P Q)
def raiseS (K:Strut c): Equiv.Perm (Support f):= Equiv.finsetCongr (act (raise s K))
abbrev driveD (W:Strut c)(T:Spike)(l:Site f→ℂ)(F: Land f D V) : Land f D V := fun i j U=>
  let x:= (P.shiftP W).symm i; let y:= (Q.shiftP W).symm j; tips (raise s W) l T (g x) (h y) (F x y ((raiseS s W).symm U))

abbrev driveC (W:Strut c)(F: Pays f D V): Pays f D V:=fun i j U=> F ((P.shiftP W).symm i) ((Q.shiftP W).symm j) ((raiseS s W).symm U)

lemma costs {F:Grid f→ArrayL D V} {X:Land f D V}{Y:Pays f D V}(K: Pack g h δ t m F A X Y) (he: Tow s P Q F)(W:Strut c)(T:Spike)(l:Site f→ℂ)(hv:Warrant (raise s W) l T):
   Pack g h δ t m F A (driveD s P Q W T l X) (driveC s P Q W Y):=by
    have hi x y : duel (driveC s P Q W Y) (P.shiftP W x) (Q.shiftP W y) t m=duel Y x y t m:=by
      unfold duel; rw [← Equiv.sum_comp (raiseS s W)]; refine sum_congr rfl fun i _=>?_ ; simp only [driveC,Equiv.symm_apply_apply]; unfold Run.rent; rw [show raiseS s W i= i.image (act (raise s W)) from Finset.map_eq_image .., cover_map (act (raise s W)) (Push.Local.turn_sep _ _)]
    constructor
    · intro i j U; obtain ⟨i,rfl⟩:= (P.shiftP W).surjective i; obtain ⟨j,rfl⟩:=(Q.shiftP W).surjective j; obtain ⟨U,rfl⟩:=(raiseS s W).surjective U
      simp only [driveC,driveD,Equiv.symm_apply_apply]; rw [P.bills,Q.bills,show raiseS s W U=U.image (act (raise s W)) from Finset.map_eq_image ..]; exact pockets (K.crop ..) hv
    · intro i j U
      obtain ⟨i,rfl⟩:= (P.shiftP W).surjective i; obtain ⟨j,rfl⟩:=(Q.shiftP W).surjective j
      rw [← Equiv.sum_comp (raiseS s W)]; simp only [driveD, Equiv.symm_apply_apply,tips,still, ← Matrix.sum_mul, ← Matrix.mul_sum]
      rw [K.sells,stages he W U l T hv, ← mul_assoc,← mul_assoc,(license hv (g i)).1,one_mul,Matrix.mul_assoc,(license hv (h j)).1,mul_one]
    · intro i; obtain ⟨i,rfl⟩:=(P.shiftP W).surjective i
      rw [← Equiv.sum_comp (Q.shiftP W)]; simp_rw [hi]; exact K.spends _
    intro j; obtain ⟨j,rfl⟩:=(Q.shiftP W).surjective j; rw [← Equiv.sum_comp (P.shiftP W)]; simp_rw [hi]; exact K.dues _
end YM.QCD.Bay
