import YM.QCD.Jets.Stops
/-! # functional readers -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets.Sun
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v:ℝ}{l:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h
variable {T:Grid f→Sheet f}(P:Sun G c f h δ v q u a l T)

lemma within_house (r:ℕ) (i:Tr f): LocalOn (roomK i) (fun U=> (mapQ P.X P.Z P.V r i (settled U):EndA R)) :=by
  cases i
  next i=>
    intro U V H; apply congr_arg (pond (ha c f F)); ext a b; rw [hook_eq,hook_eq]; rw [show P.X _ _ i (settled U) = P.X _ _ i (settled V) from (P.X0.crop _ _ i).2.2.2.2.1 U V H] -- check
  next i=>
    intro U V H; apply congr_arg bark; ext a b; unfold longP; cases a <;> cases b
    · rw [foamI,foamI,show P.Z _ _ i (settled U)=P.Z _ _ i (settled V) from (P.Z0.crop _ _ i).2.2.2.2.1 U V H]
    · rfl
    · rfl
    rw [foamR,foamR,show P.V _ _ i (settled U)=P.V _ _ i (settled V) from (P.V0.crop _ _ i).2.2.2.2.1 U V H]
lemma closer (i:Keys f F)(j: Keys c F)(r:ℕ): LocalOn (halo r {locationP i}) fun U=> short P.Z P.V r (settled U) i j:=by
  intro U V H; change short P.Z P.V r (settled U) i j= short P.Z P.V r (settled V) i j; unfold short; cases i <;> cases j
  next a b=> rw [foamI,foamI]; split; · apply congrFun; apply congrFun; exact (trimming P.Z0 _ _ _ _).2.2.2.2.1 U V H
             rfl
  next=>rfl
  next=>rfl
  next a b=> rw [foamR,foamR]; split; · apply congrFun; apply congrFun; exact (trimming P.V0 _ _ _ _).2.2.2.2.1 U V H
             rfl
lemma breeze {X:Pulse f→Bundle}{p x y}(H:Crop x y δ p X κ)(hv:0<δ): Continuous (fun U:Grid f=> X (settled U)):=by
  have ht: Continuous (settled: Grid f→Pulse f):=by unfold settled; fun_prop
  exact continuous_iff_continuousAt.mpr fun i=> (H.2.2.1 _ (citizenship f hv i)).continuousAt.comp ht.continuousAt
lemma pond_s (Q : Matrix A A ℂ): Continuous (pond (ha c f F)):=by
   unfold pond; refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=> ?_; fun_prop
lemma bark_s : Continuous (bark : Water c f F→ EndA R):=by
   unfold bark barkG; refine continuous_finsetSum _ fun i _=> continuous_finsetSum _ fun j _=>?_ ; fun_prop
lemma curved (r : ℕ): Continuous (fun U=> (short P.Z P.V r (settled U): Water c f F)):=by
  refine continuous_pi ?_; intro i; refine continuous_pi ?_; intro j; cases i <;> cases j
  next i j=> unfold short; simp_rw [foamI]; split; · exact (continuous_apply _).comp ((continuous_apply _).comp (breeze (trimming P.Z0 _ _ _ _) P.positive))
             exact continuous_const
  next=>exact continuous_const
  next=>exact continuous_const
  next i j=> unfold short; simp_rw [foamR]; split; · exact (continuous_apply _).comp ((continuous_apply _).comp (breeze (trimming P.V0 _ _ _ _) P.positive))
             exact continuous_const
lemma arced (r:ℕ) (i:Tr f) : Continuous (fun U=> (mapQ P.X P.Z P.V r i (settled U):EndA R)):=by
  cases i
  next i=>
   apply (pond_s (c:=c) (F:=F) (f:=f) 0).comp (f:=fun U:Grid f=> ship P.X i (settled U)); refine continuous_pi fun a=> continuous_pi fun b=>?_ ; simp_rw [hook_eq]; split; · exact (continuous_apply _).comp ((continuous_apply _).comp (breeze (P.X0.crop _ _ i) P.positive))
   exact continuous_const
  next i=>
   apply bark_s.comp (f:=fun U:Grid f=> longP P.Z P.V r (settled U) i)
   refine continuous_pi fun a=> continuous_pi fun b=>?_
   unfold longP; cases a <;> cases b
   next a b=>
     simp_rw [foamI]; split
     · by_cases hh:i∈satZip a.1.1 r <;> simp only [hh, ↓reduceIte]; · exact (continuous_apply _).comp ((continuous_apply _).comp (breeze (P.Z0.crop _ _ i) P.positive))
       exact continuous_const
     exact continuous_const
   next=>exact continuous_const
   next=>exact continuous_const
   next a b=>
    simp_rw [foamR]; split
    · by_cases hh:i∈satZip a.1.1 r <;> simp only [hh, ↓reduceIte]; · exact (continuous_apply _).comp ((continuous_apply _).comp (breeze (P.V0.crop _ _ i) P.positive))
      exact continuous_const
    exact continuous_const

-- no field-dependent footprint

def equip (F r:ℕ): Cove.Send S F (Tr f) where
 rooms i:= roomK i
 trim:=r
 shortP U:= short P.Z P.V r (settled U)
 treats i U:= mapQ P.X P.Z P.V r i (settled U)
 hat := fun _ _ _=> cash ..
 weld U i:= town P (settled U) r (citizenship f P.positive U) i
 fuel :=fun _ _=>cash_zero ..
 stance:=within_house P r
 shortens i j:=closer P i j r
 sleeps i j U:=lightS P (settled U) r (citizenship f P.positive U) i j
 vibe:= P.curved r
 river:=P.arced r
end YM.QCD.Jets.Sun
