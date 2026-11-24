import YM.Massive.Stratum.Range
import YM.Massive.Stratum.Grind
/-!
# Shape constraints and the network of post-L budgets

This schedule is laid out once and for all. For any stream of requested
extra expenses that depend only on the **type of step** (not where in the schedule!),
including its incoming and outgoing price sheet upper bounds, can include them,
with their growth at most a constant plus `# steps to reference`.
This also supports asking for arbitrarily frequent startup-only moment costs by
using a combined charge per type; it does *not* mean infinitely many arbitrary simultaneous
requests are allowed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {j:ℕ}

def loomPow (j:ℕ)(he:4≤j)(i:ℕ): Flight j j:= ⟨(3:Side)^(i+1), by rw [ PNat.pow_coe]; exact (show Odd (3:ℕ) from by decide).pow, by
    rw [PNat.pow_coe]; change 3 ≤ (3:ℕ)^_
    simpa using pow_le_pow_right₀ (by decide: 1 ≤ (3:ℕ)) (show 1 ≤ i+1 from by omega), he,le_rfl,by omega,Train.top j⟩

theorem lim_pow (he:4≤j): Tendsto (fun i=> ((loomPow j he i).L.val:ℕ)) atTop atTop:= (tendsto_pow_atTop_atTop_of_one_lt (by decide : (1:ℕ) < 3)).comp (tendsto_add_atTop_nat 1) -- check defeq

structure AtlasH (Q:Rock j)(J:Plan j)(p:ChartRatio su) where
  path : ℕ→Flight j j
  towns : ℕ→Town
  gap : ℕ→ℝ
  cost : ℕ→ℝ
  marine :ℕ→ParcelR
  boat i : Dispatch Q J (path i) (towns (i+1)) (towns i) p (gap i) (cost i) (marine i)
  powers i:∃ j:ℕ,(path i).L.val=3^j
  slopes i:(path i).L.val ≤ (path (i+1)).L.val
  gradual i:(path (i+1)).L.val ≤3*(path i).L.val
  free : Tendsto (fun i=>(path i).L.val) atTop atTop

variable (Q:Rock j)(J:Plan j)(p: ChartRatio su)

-- Opaque need & minimum block side (determined by other chapters).
theorem atlasH (K': ℕ)(hj:4≤j)(hp:LocalRatio p) (hw:∀ E:Patch,E.Branches Q.Z.bind su)
    (need: Flight j j→Town→Town→ℝ→ℝ→ParcelR→ℝ):
    ∃ (A:AtlasH Q J p)(B:ℕ),∀ i:ℕ,K'≤ (A.path i).L.val ∧ need (A.path i) (A.towns (i+1)) (A.towns i) (A.gap i) (A.cost i) (A.marine i) ≤ (i:ℝ)+B:=by
   obtain ⟨n,hn⟩:=regime Q J hj
   obtain ⟨m,H⟩:= eventually_atTop.mp ((lim_pow hj).eventually_ge_atTop (n+Q.n+K'))
   let S i := loomPow j hj (i+m)
   have hL i : n+Q.n+K' ≤ (S i).L.val:= H _ (by omega)
   let R i:=Flown Q J (S i).patch
   have hr (i:ℕ):Century (R i):= hn _ (le_trans (by omega) (hL i)) -- ambiguity
   have he(i:ℕ) (X Y:Town) (h:R i X Y) : ∃ a b Ω, Dispatch Q J (S i) X Y p a b Ω:= signal_dispatch Q J X Y _ ((by omega : Q.n ≤ n+Q.n+K').trans (hL i)) hp (hw _) h
   let _:Nonempty ParcelR:=⟨⟨1,1,1,1,1,1,1,1,1⟩⟩
   choose! a b P hx using he
   let N i x y := ⌈need (S i) x y (a i x y) (b i x y) (P i x y)⌉₊
   obtain ⟨A⟩:= deploy R N hr
   let M i:=A.height i; let z:= A.sites
   let X i:= S (M i); have hf i: (X i).L.val= (3:ℕ)^(M i+m+1):=by unfold X S loomPow; simp
   let F:AtlasH Q J p:= {
                            path:= X
                            towns:=z
                            gap:=fun i=> a (M i) (z (i+1)) (z i)
                            cost:=fun i=>b (M i) (z (i+1)) (z i)
                            marine:=fun i=>P (M i) (z (i+1)) (z i)
                            boat:=fun i=> hx _ _ _ (A.links i)
                            powers:=fun i=>⟨_,hf i⟩
                            slopes:=fun i=>by rw [hf,hf]; have hh:M i ≤ M (i+1):=A.grows i; exact pow_le_pow_right₀ (by decide:1 ≤ (3:ℕ)) (by omega)
                            gradual:=fun i=>by
                              have hh: M (i+1) ≤ M i+1:=A.stays i
                              rw [hf,hf,mul_comm,← pow_succ]
                              exact pow_le_pow_right₀ (by decide:1 ≤ (3:ℕ)) (by omega)
                            free:=(lim_pow hj).comp (show Tendsto (fun i=> M i + m) atTop atTop from tendsto_atTop_mono (fun i=>by unfold M; omega) A.free) }
   refine ⟨F,N 0 (z 1) (z 0),fun i=>⟨(by omega : K'≤ n+Q.n+K').trans (hL _),?_⟩⟩
   have hh: (↑(N (M i) (z (i+1)) (z i)):ℝ) ≤ (i:ℝ) + N 0 (z 1) (z 0):= by
        exact_mod_cast A.enough i
   exact (Nat.le_ceil _).trans hh
end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.atlasH
