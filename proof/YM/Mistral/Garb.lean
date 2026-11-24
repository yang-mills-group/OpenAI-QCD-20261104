import YM.Mistral.Wals
import YM.Bwana.Mono
import YM.Intag.Cavity
import YM.Needle.Slots
/- layout common T at ANY desired summit/margin. pay external by higher spacing if necessary. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Hub
open Set Filter Function Finset Lattice Source
open scoped ContDiff Topology BigOperators Classical
open QCD QCD.Lat UV Cylinder RG Wilson Grass MeasureTheory Cells QCD.RP
open Massive.Romance Poised Plans Display Poised.Plans Stamp
open Massive.Patria.Depth Intag Next.Rank.Station
namespace Duon
variable {S: Massive.Scheme}{C n R:Side}{i k m j:ℕ}{x:ℝ}
variable (g:Ratio C n)(hC:Even C.val)
lemma wingsW (f:Fin m→ Site n)(K:Fin m→ℕ)(h:∀ i,0<K i)(hp:(∑ i, 2*K i)< g.count.val) : ∃ z:Site n,∀ i,∃ p:Site C,f i∈(mural g hC z).margin p (K i):=by
     let T:= mural g hC (0:Site n); obtain ⟨z,hz⟩:= T.fits_weight f K h hp; let x:Site n:= fun i=> z i+((g.count.val/2:ℕ):Per n); let B:=mural g hC x
     have hB:T.newly z = B :=by unfold Tiling.newly T B mural; congr 1; funext i; dsimp only [x]; rw [add_sub_cancel_right]
     refine ⟨x,fun i=>?_⟩; have ht:(∃ p:(T.newly z).Cell,f i∈ (T.newly z).margin p (K i)):=⟨(T.newly z).which _,hz i⟩; rw[hB] at ht; exact ht
variable {ℓ N:ℕ}(R:Side)(he:Even R.val)(hz: j ≤ ℓ)(hp:ℓ ≤ N)
local notation "φ"=>S.side R
local notation "VE"=>viewW S R
local notation "X"=> viewW S R hp
local notation "Y_"=> viewW S R hz
local notation "Fv"=> viewW S R (hz.trans hp)
local notation "LX"=>ratioTo S ℓ j
local notation "It"=> Fin (m+1)
local notation "v_"=>evenW S R he
local notation "ℓX"=> ratioTo S N ℓ
local notation "S_"=> ratioTo S ℓ (j+1)
variable (M:ℕ)
set_option quotPrecheck false
-- funding.Seam.Success. π. discrete winding.Str for Aura
include hz hp
lemma smeared (z:Site (φ ℓ))(p:Site (φ j))(x:Site (φ N))(h:(viewW S R hp).parent x ∈ (Column.sky S R j ℓ hz (evenW S R he j) z).margin p (M+1)): x∈ (Column.sky S R j N (hz.trans hp) (evenW S R he j) z).margin p ((viewW S R hp).count.val*M):=by
      unfold Column.sky at h; rw [Column.homes] at h
      let f:=viewW S R hp; have hv:= (stepSpan Y_ f Fv z (f.parent x) p (v_ j) (odd_to hz) (odd_to hp) _).1 h
      unfold Column.sky; rw [key_margin Fv _ _ _ _ (odd_to (hz.trans hp))]; unfold Column.pillar; rw [dif_pos hp]
      let b:=(f.embed z)+(Fv).embed p; have ht:separation (f.embed (f.parent x)) b+ f.count.val*(M+1) ≤ (Fv).count.val/2:= (key_margin Fv _ _ _ _ (odd_to (hz.trans hp)) _).1 hv; have hP:= midway f (odd_to (S:=S) hp) x
      have he:separation x b≤ separation x (f.embed (f.parent x))+ separation (f.embed (f.parent x)) b:=separation_triangle ..; change separation x b + f.count.val*M ≤ (Fv).count.val/2; rw [mul_add,mul_one] at ht; omega
lemma curtains (z:Site (φ ℓ))(p:Site (φ j))(x:Site (φ N))(h:x∈ (Column.sky S R j N (hz.trans hp) (evenW S R he j) z).margin p M)(hM: i*ratioTo S N ℓ+ratioTo S N ℓ ≤ M) : (viewW S R hp).parent x ∈ (Column.sky S R j ℓ hz (evenW S R he j) z).margin p i:=by -- maybe not needed. remove
       unfold Column.sky; rw [Column.homes]; apply (stepSpan Y_ X Fv z ((X).parent x) p (v_ j) (odd_to (S:=S) hz) (odd_to (S:=S) hp) i).2
       rw [key_margin Fv _ _ _ _ (odd_to (hz.trans hp))]; let f:=X; let k:=(f.embed z)+(Fv).embed p; unfold Column.sky Column.pillar at h; rw [dif_pos hp] at h
       have ht:separation x k+M ≤ (Fv).count.val/2:= (key_margin Fv _ _ _ _ (odd_to (hz.trans hp)) M).1 h; have hB:= midway f (odd_to (S:=S) hp) x; have hv:= separation_triangle (f.embed (f.parent x)) x k; rw [separation_comm (f.embed (f.parent x)) x] at hv; change separation (f.embed (f.parent x)) k+f.count.val*i≤ _; have hk:i*f.count.val+f.count.val≤ M:=hM; rw [Nat.mul_comm i] at hk; omega
-- passports.Data.External marks chamber distinct, chosen simultaneous.Weight variable. he counts Slope.EQ true.
variable (p:Cover)(v:Fin (m+1) → Site (S.side R N))(hX:∀ i k:Fin (m+1),i≠k → (ratioTo S N j) < separation (v i) (v k))(K:ℕ)
include hX
set_option maxHeartbeats 450000 in
lemma housing (hD:j+1≤ ℓ)(ht: 16*K +32≤ ratioTo S ℓ j)(hC0: 40*(m+1) ≤ (S.step j).L.val) : ∃ (c: Site (S.side R ℓ))(p:It→ Site (S.side R j)), Injective p ∧ (viewW S R hp).parent (v 0) ∈ (Column.sky S R j ℓ hz (evenW S R he j) c).margin (p 0) (K+1) ∧∀ i:Fin m,v i.succ∈ (Column.sky S R j N (hz.trans hp) (evenW S R he j) c).margin (p i.succ) (3*ratioTo S N (j+1)):=by
      let u:Fin (m+1)→ℕ:= Fin.cons (K+1) (fun _=>3*(ratioTo S ℓ (j+1))+1); let v':= (X).parent∘ v; have hx(q:It):0<u q:=by induction q using Fin.cases <;> simp [u]
      let d:=ratioTo S ℓ (j+1); have h':0<d:=(odd_to hD).pos; have hh : (∑ i:It,2*u i)< LX:=by
           rw [Fin.sum_univ_succ]; simp [u]; rw [step_factor hD]; have hp:= Nat.mul_le_mul_right d hC0; rw [step_factor hD] at ht; change _≤ (S.step j).L.val*d at ht; change _+m*(2*_)< _*d; nlinarith only [ht,hC0,h',hp,Nat.zero_le m]
      obtain ⟨z,hz'⟩:= wingsW Y_ (v_ j) v' u hx hh; choose q hq using hz'; have hv (i:It): v' i∈ (Column.sky S R j ℓ hz (evenW S R he j) z).margin (q i) (u i):=by unfold Column.sky; rw [Column.homes]; exact hq i
      let T:= Column.sky S R j N (hz.trans hp) (v_ j) z; have hV(i:Fin m): v i.succ∈ T.margin (q i.succ) (3*ratioTo S N (j+1)):=by have h:=smeared R he hz hp (3*d) z (q _) _ (show v' i.succ∈ _ from hv i.succ); rw[Off.ruler (S:=S) hD hp]; convert h using 2; change 3*(_*d)= (ratioTo S N ℓ)*_; ring
      have ht0:v 0∈ T.margin (q 0) (ratioTo S N ℓ*K):=smeared R he hz hp K z _ _ (hv _)
      have htA(i:It):v i∈ T.chamber (q i):=Fin.cases ht0.1 (fun k=> (hV k).1) i
      refine ⟨z,q,fun i k hi=>?_,hv 0,hV⟩; by_contra hy; exact Nat.not_lt_of_ge (show separation (v i) (v k)≤ T.side.val from T.extent (htA i) (show v k∈ T.chamber (q i) from hi.symm ▸ htA k)) (hX i k hy)
end Duon
end YM.Massive.Patria.Hub
#print axioms YM.Massive.Patria.Hub.Duon.housing
