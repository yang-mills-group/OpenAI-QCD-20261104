import YM.Massive.Filament.Loop
/-! Keep analyticity for arrays after each flagged merge with ℂ colors. Useful for normal thermal branches where Soft shift is picked only once. `Arc` statement, evaluation variant for future cross-family “act” proof. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fibre
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Kites
open Massive.Filament
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N B:ℕ}{h A R C D W r:ℝ}{s z:ℂ} {ι α: Type}
variable (X: ℂ → ℂ → Rail c N ι)
open Ruby Fused
local notation "V"=> EvenA c N
variable (Y: ℂ→ℂ→ Ruby.Hue c N α)
-- Use brace even off domains; sufficient to assert Definitional Equality at X0 is typical when writing. Arc hypotheses on editable own entries.
structure Arch: Prop where
 bud (z s:ℂ): (Y z s).bud=(Y 0 0).bud
 reading (i:α)(U:Grid c): Fused (fun z s=> (Y z s).mean i U)

abbrev welded (z s:ℂ) : Ruby.Hue c N α:= ⟨(Y 0 0).bud, (Y z s).mean⟩
abbrev loose (z s:ℂ) : Rail c N ι:=⟨(X 0 0).addr, (X z s).warp⟩
lemma Arch.equal (hp:Arch Y)(z s:ℂ) : welded Y z s=Y z s:=by unfold welded; rw [← hp.bud z s]
lemma Arc.equal (hp:Arc X)(z s:ℂ): loose X z s=X z s:=by unfold loose; rw [← hp.brace z s]
abbrev glen (z s:ℂ) (t:ℝ): Rail c N (Plot (Y 0 0) (X 0 0)):= Trail (welded Y z s) (loose X z s) t
lemma Arc.trail (t:ℝ)(hp:Arc X)(hP:Arch Y): Arc (fun z s=> glen X Y z s t):=by
   refine ⟨fun _ _=>rfl, fun i U=>?_⟩
   let F z s (j:Stamp α ι):= flower (welded Y z s) (loose X z s) U j
   change Fused (fun z s=> ite (RG.flags t U∩ scopeK (Y 0 0) (X 0 0) i.val=badgeK (X 0 0) i.val) (∏ k∈ i.val,F z s k) 0)
   by_cases h : RG.flags t U ∩ scopeK (Y 0 0) (X 0 0) i.val=badgeK (X 0 0) i.val
   swap; · simp_rw [if_neg h]; exact steady _
   simp_rw [if_pos h]; apply Fused.multiple (fun k z s=> F z s k) i.val
   rintro (i|i) _; · exact hp.reading i U
   exact (hP.reading i U).exponential.minus (steady (1:EvenA c N))
lemma constantArch (J: Ruby.Hue c N α): Arch (fun _ _=>J):=⟨fun _ _=> rfl, fun _ _=> steady _⟩
lemma constantArc (J:Rail c N ι): Arc (fun _ _=>J):=⟨fun _ _=>rfl,fun _ _=>steady _⟩
lemma Arc.spark (t:ℝ)(hp:Arc X): Arc (fun z s=> flightK (X z s) t):=by
   refine ⟨fun z s=>hp.brace _ _, fun i U=>?_⟩
   let L:EvenA c N→L[ℂ] EvenA c N:= ⟨(wearK c N t).toLinearMap, (songT (c:=c) (N:=N) t).continuous⟩
   exact (hp.reading i U).compose L (by fun_prop)
end YM.QCD.Fibre
#print axioms YM.QCD.Fibre.Arc.trail
