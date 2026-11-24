import YM.QCD.Jets.Slide
/-! # State matters. Render Pack for positive torso. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Jets
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {F k j:ℕ}{c f: Side} {δ q κ a u v:ℝ}{l:ℕ}{G:Flight j k}{h:f.val=c.val*G.L.val}
local notation "A"=> Modes f F
local notation "B"=> Modes c F
local notation "R"=> Junta c f F
local notation "S"=> sliceL G h

-- package call independent. Binders
structure Sun (G: Flight j k) (c f:Side)(h:f.val=c.val*G.L.val)(δ v q b a:ℝ)(l:ℕ)(T:Grid f→Sheet f) where
 positive :0<δ
 stable : Species G h v q δ b a l T
 X: Land f (Site f) (Site f)
 Y: Pays f (Site f) (Site f)
 X0: Pack id id δ b l (inverser T) q X Y
 Z: Land f (Site f) (Site c)
 W: Pays f (Site f) (Site c)
 Z0: Pack id (sliceL G h).embed δ b l (rightL G h T) q Z W
 V: Land f (Site c) (Site f)
 B0: Pays f (Site c) (Site f)
 V0:Pack (sliceL G h).embed id δ b l (leftL G h T) q V B0

variable {T:Grid f→Sheet f}
lemma sun_nonempty (H:Species G h v q δ u a l T)(he:0<δ): Nonempty (Sun G c f h δ v q u a l T):=by obtain ⟨x,y,Q⟩:= H.hashed; obtain ⟨M,p,hp⟩:=H.links; obtain ⟨z,w,hw⟩:=H.reigns; exact ⟨⟨he,H,x,y,Q,z,w,hw,M,p,hp⟩⟩

variable (P:Sun G c f h δ v q u a l T)
namespace Sun

def roomK (i:Tr f): Support f:=Sum.elim id id i
-- support witness
lemma farmhouse {V: Pulse f→Bundle}{i j : Site f}{U:Support f}{I: Pulse f}{x y:Fiber}(ht: Crop i j δ U V κ)(hp:I∈Kingdom f δ)(h:V I x y ≠ 0): κ≠0 ∧ i∈U ∧ j∈U:=by
  have hg :V I ≠0:= fun he=> h (he ▸ rfl) -- dependent trouble
  have hv := (norm_pos_iff.mpr hg).trans_le (ht.2.2.2.1 I hp); exact ⟨hv.ne',ht.2.1 hv.ne'⟩

variable (Q:Pulse f)(r:ℕ) (hp: Q∈Kingdom f δ)
include hp
lemma town (i:Tr f): Stays (excess (mapQ P.X P.Z P.V r i Q)) (hooks (F:=F) (sliceL G h) (roomK i)):=by
  cases i
  next i=>
   apply Stays.ink; intro a b ht
   change ship P.X i Q a b≠0 at ht; rw [hook_eq] at ht; split at ht
   · have hx:=farmhouse (P.X0.crop _ _ i) hp ht; exact ⟨(hooked ..).2 (by rw [pet,rootA]; exact hx.2.1), (hooked ..).2 (by rw [met,rootA]; exact hx.2.2)⟩
   exact (ht rfl).elim
  next i=>
   apply Stays.sunray; intro a b ht; change longP P.Z P.V r Q i a b≠0 at ht; rcases a with a|a <;> rcases b with b|b
   · unfold longP at ht; rw [foamI] at ht; split at ht
     · split at ht
       · have hm:=farmhouse (P.Z0.crop _ _ i) hp ht; change ha _ _ _ _∈_ ∧ hb _ _ _ _∈_; rw [hooked,hooked,rootA,rootB]; exact hm.2
       exact (ht rfl).elim
     exact (ht rfl).elim
   · exact (ht rfl).elim
   · exact (ht rfl).elim
   unfold longP at ht; rw [foamR] at ht; split at ht
   · split at ht
     · have hm:=farmhouse (P.V0.crop _ _ i) hp ht; change ha _ _ _ _∈_ ∧ hb _ _ _ _∈_; rw [hooked,hooked,rootA,rootB]; exact hm.2.symm
     exact (ht rfl).elim
   exact (ht rfl).elim
lemma lightS (i:Keys f F)(j:Keys c F)(h₀: short P.Z P.V r Q i j≠0): (S).embed (locationP j) ∈ halo r {locationP i}:=by
 unfold short at h₀; cases i <;> cases j
 · rw [foamI] at h₀; split at h₀; · exact (farmhouse (trimming P.Z0 _ _ _ _) hp h₀).2.2
   exact (h₀ rfl).elim
 · exact (h₀ rfl).elim
 · exact (h₀ rfl).elim
 rw [foamR] at h₀; split at h₀; · exact (farmhouse (trimming P.V0 _ _ _ _) hp h₀).2.1
 exact (h₀ rfl).elim
omit hp
end Sun
end YM.QCD.Jets
