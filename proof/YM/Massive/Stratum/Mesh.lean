import YM.Massive.Stratum.Burg
import YM.QCD.Disc.Echo
/-! # Aspect

Keep the prescribed **per-step** auxiliary meshes for uniform cost derivations
while lifting each also through the unbounded physical volume chosen at this depth.
No price payment by an upper limit on period.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre.Stratum
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open Flume Fog.Mist YM.Massive.Stratum Push ConnectedActivityE6 Pressure Pressure.Stores Revolve Rudder Eyrie
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
variable {j n i k:ℕ}{Q:Rock j}{J:Plan j}{p:ChartRatio su} (Y:AtlasH Q J p) {b:SparkMesh}
local notation "Qq" => Q.Z.top.clip
local notation "Kq" => Q.Z.bind
local notation "u₀" => Q.Z.top.width
open AtlasH
open Fog.Voyage
variable {S:ℕ→SparkMesh}
def refrain (i:ℕ):Side := 2*(3:Side)^i

def accord (k:ℕ): SparkMesh where
  n i:=refrain (i+k)
  cofinal:=by
     refine tendsto_atTop_mono ?_ (tendsto_pow_atTop_atTop_of_one_lt (show 1 < (3:ℕ) from by decide)); intro i
     change (3:ℕ)^i ≤ 2*3^(i+k); exact (pow_le_pow_right₀ (by decide : 1≤ (3:ℕ)) (by omega : i≤ i+k)).trans (Nat.le_mul_of_pos_left _ (by omega))
  ratio i j :=3^(j-i)
  factor i j h:=by simp [refrain,mul_assoc,← pow_add]; rw [show i+k+(j-i)=j+k from by omega]
  parity _ _ _:= (show Odd (3:ℕ) from by decide).pow
lemma chord (i:ℕ):∃ d:ℕ,Y.orbit i=(3:Side)^d:=by
    induction i with
    | zero=> exact ⟨0,by simp⟩
    | succ i ih=>
       obtain ⟨d,h⟩:= ih; obtain ⟨s,hS⟩:= Y.powers i
       have hp:Y.length i=(3:Side)^s:=by apply Subtype.ext; change (Y.length i).val = ((3:Side)^s).val; exact hS.trans (by simp)
       exact ⟨d+s,by rw [orbit,h,hp,pow_add]⟩
lemma chord_head (i:ℕ)(v:ℕ)(x:ℝ):∃ d:ℕ,head (Y.length i) v x=(3:Side)^d:=by
    obtain ⟨d,hD⟩:= Y.powers i
    refine ⟨d*rootX (Y.length i) v x,?_⟩; apply Subtype.ext; change ((Y.length i)^_).val = ((3:Side)^_).val; rw [PNat.pow_coe,PNat.pow_coe,pow_mul]; simp only [AtlasH.length,hD]; rfl

omit Y in
theorem refrain_even (i:ℕ): Even (refrain i).val:=by unfold refrain; rw [PNat.mul_coe]; exact Even.mul_right (by decide : Even (2:ℕ)) _
theorem orbit_sound (b i k:ℕ):∃ l:ℕ,b+i≤l ∧ Y.ring ((accord b).n i) k=refrain l :=by
   obtain ⟨l,hL⟩:= chord Y k; change ∃ l:ℕ,b+i≤l ∧ Y.ring (refrain _) k=_
   exact ⟨i+b+l,(by omega),by rw [AtlasH.ring,hL]; simp [refrain,pow_add,mul_assoc]⟩

open PhysicalNext.Repeat Slide -- check
lemma plane (M:ℕ) (v:ℕ→ℕ)(x:ℕ→ℝ): ∀ᶠ k:ℕ in atTop, ∃ S:ℕ→SparkMesh, Align Y (accord k) S M ∧ ∀ i:ℕ, i < M →
  let Q:= head (Y.length i) (v i) (x i); (∀ j:Stars,(S i).n j.val=stellar Q j.val)∧∀ j:ℕ,2*style (Y.length i) (v i) (x i)< ((S i).n (j+5)).val:=by
    let B i:= head (Y.length i) (v i) (x i)
    let t i:=2*style (Y.length i) (v i) (x i)
    have hw (i):∀ᶠ k:ℕ in atTop, let A:=ratioM (Y.orbit i) (accord k);
         t i < (A.n 0).val ∧ bonds (stellar (B i) 4) (A.n 0):=by
        have hp: Tendsto (fun k=>(Y.ring ((accord k).n 0) i).val) atTop atTop:=by
           have he:=ringing Y (accord 0) i
           have heh : Tendsto (fun k=>(Y.ring ((accord 0).n k) i).val) atTop atTop:=tendsto_atTop.mpr (fun b=> by
                filter_upwards [he.eventually_ge_atTop (⟨b+1,by omega⟩:Side)] with j hj; exact le_trans (Nat.le_succ _) hj)
           apply heh.congr'; filter_upwards with j; change (Y.ring (refrain _) _).val=(Y.ring (refrain _) _).val; rw [Nat.zero_add,Nat.add_zero]
        obtain ⟨d,hD⟩:=chord_head Y i (v i) (x i); change B i=_ at hD; filter_upwards [hp.eventually_gt_atTop (t i), eventually_ge_atTop (d+4)] with k hk h
        intro A; refine ⟨hk,?_⟩
        obtain ⟨b,hb,H⟩:=orbit_sound Y k 0 i
        let a:=b-(d+4); have hy:d+4+a=b:=by unfold a; omega
        refine ⟨3^a,?_, (by decide : Odd (3:ℕ)).pow⟩; change (Y.ring ((accord k).n 0) i).val=_; rw [H,hD,← hy]; simp[refrain,pow_add,stellar]; ac_rfl
    have hf : ∀ᶠ k:ℕ in atTop,∀ i:Fin M,t i < ((ratioM (Y.orbit i) (accord k)).n 0).val ∧ bonds (stellar (B i) 4) ((ratioM (Y.orbit i) (accord k)).n 0):= eventually_all.mpr (fun i=> hw i.val)
    filter_upwards [hf] with k hk; let A i:=ratioM (Y.orbit i) (accord k)
    have he(i:ℕ)(hi:i<M):= crew (B i) (A i) (hk (⟨i,hi⟩: Fin M)).2
    letI :Nonempty SparkMesh:=⟨accord k⟩
    choose! P hv hL using he
    -- result
    refine ⟨P,⟨fun i hi j=>hL i hi j⟩,fun i hi=>⟨hv i hi,fun j=>?_⟩⟩; rw [hL i hi]; exact ((hk ⟨i,hi⟩).1).trans_le (crest_mon (A i) _ _ (by omega))

end YM.QCD.Acre.Stratum
#print axioms YM.QCD.Acre.Stratum.plane
