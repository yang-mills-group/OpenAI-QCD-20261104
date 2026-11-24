import YM.QCD.Door.Coast
/-! # chiral bars. Flavors. -/
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
variable {G:Grid f→Sheet f}{δ a b c' q:ℝ}{l:ℕ} {P:Sun L c f H δ a b c' q l G}

lemma tagP (F:Site f→Site c→Bundle)(Y: Site c→Site f→Bundle)(h:∀ i j,Y i j=J0*star (F j i)*J0): openK Y= foldH (openK F):=by
   apply whist; intro i j; rw [foldH,← terraJ (D:=Site f)]; unfold terraL; rw [cell_ride_right,cell_ride_left,cell_flip,cT]; exact h i j
lemma glyph (hp: Sacred P)(i: Support f)(x:Grid f): flowY P i x= foldH (flowY P i x):=tagP (fun a b=>P.X a b i (settled x)) (fun a b=>P.X a b i (settled x)) (by
   -- target RHS type infer
   intro a b; have hx: P.X a b i _ =_:= congrFun (congrFun (congrFun (congrFun hp.chiral.symm a) b) i) (settled x); unfold seed at hx; rw [fullT] at hx; exact hx)
lemma grim (b:ℕ)(hp:Sacred P)(i:Support f)(x:Grid f): tailsF P b i x=foldH (heads P b i x):=by
   apply tagP; intro a k; unfold seatV seatL; split; · rw [← hp.friendly]; unfold seed; rw [fullT]
   simp
lemma wising (b:ℕ)(hp:Sacred P)(x:Grid f): rP P b x=foldH (rL P b x):=by
   apply tagP; intro a k; unfold seatS seatA spoon; rw [← hp.friendly]; simp only [Finset.sum_apply,seed,fullT,star_sum,Matrix.mul_sum,Matrix.sum_mul]

-- ring motion exact flavor all. right module canon. U(F) includes charge tests. K1 retains same transformations across levels.
def flute (D:Type*)[DecidableEq D](V:Matrix (Flavor F) (Flavor F) ℂ): Matrix (D × Flavor F) (D×Flavor F) ℂ:= Matrix.kronecker (1:Matrix D D ℂ) V
lemma choir_in {D V:Type*}[DecidableEq D][DecidableEq V] (X:Matrix D V ℂ) (K:ℕ): choir K X=Matrix.kronecker X 1 :=by
  ext ⟨i,a⟩ ⟨j,b⟩; by_cases h:a=b <;> simp [choir,Matrix.kronecker_apply,Matrix.one_apply,Matrix.blockDiagonal_apply,h]
lemma column {D V:Type*}[Fintype D][Fintype V][DecidableEq D][DecidableEq V] (W:Matrix D V ℂ)(X:Matrix (Flavor F) (Flavor F) ℂ): flute D X * choir F W = choir F W*flute V X:=by unfold flute; rw [choir_in]; unfold Matrix.kronecker; rw [← Matrix.mul_kronecker_mul,← Matrix.mul_kronecker_mul]; simp
lemma unit_f {D:Type*}[Fintype D][DecidableEq D]{X:Matrix (Flavor F) (Flavor F) ℂ}(h: X∈unitary _):flute D X∈unitary _:=by unfold flute Matrix.kronecker; constructor; all_goals rw [star_kr,star_one,← Matrix.mul_kronecker_mul]; first| rw [h.1]; simp | rw [h.2]; simp

end YM.QCD.Sway
