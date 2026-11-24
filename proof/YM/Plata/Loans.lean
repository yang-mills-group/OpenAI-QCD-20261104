import YM.Plata.Spurt
/-! aligned all-point physical stencil precision on each phase. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
open YM.Plata Function Metric Set Finset
namespace Compass
open Choir Strip
variable {Q:Choir}{C:Sequence}{P: Calibration C}{φ:ℕ→ℕ}{S:Canopy.KForm Q}
variable {D k n m:ℕ}
open MassiveQCD MassiveQCD.Sample MassiveQCD.Sample.Quills MassiveQCD.Sample.Quills.Eden Ribbon Cupola
open Quills.Clover YM.Arise.Bill YM.Arise.Count Play Play.Chamber
variable (X:Fin n→ Glyph D) (A:Compass C D)(x:Fin n→ Cover)
variable (V: Legend) (Z:ℕ→ Legend) (T:List (Fin n)) (R:Bankroll P φ Q S)
set_option quotPrecheck false
variable (g:ℕ→ℕ)
local notation "xQ" => A.qR A.ℓ ∘ x
local notation "f"=> φ ∘ g
include R
lemma condP (hF:Tendsto g atTop atTop)(hA:Known A): Tendsto (fun i=> A.qR (C.N ((φ∘g) i)) ∘ cave A x ((φ∘g) i)) atTop (𝓝 (A.qR A.ℓ ∘ x)):=by
       obtain ⟨β,e,h⟩:= R.path; have h':=(h.uv.tendsto_atTop.comp (R.flows.comp hF)).eventually_ge_atTop A.ℓ; exact tendsto_const_nhds.congr' (h'.mono fun i hi=> funext fun j=> hA.Γ.joins (x j) hi)
omit R
lemma rangesT (g:ℕ→ℕ) (T:List (Fin n))(he:T.Nodup)(h:Injective (A.qR A.ℓ ∘ x)): Strip.distinct (Plata.position (Q:=Q) (Tent X A x V Z g T)):=by
       rw [Strip.spots,Plata.position,Tent,List.map_map,List.map_map]; apply he.map; intro i j hz; change A.r • (xQ) i=A.r • (xQ) j at hz; exact h (smul_right_injective E4 A.realH.ne' hz)
include R
lemma Wsettled (T:List (Fin n))(h:Tendsto g atTop atTop)(hg:grace (D:=D) Z (φ∘g) V)(hA: Known A): Worn C (φ∘g) (Tent X A x V Z (φ∘g) T):=by
       constructor; intro p hp; obtain ⟨j,hj,rfl⟩:= List.mem_map.mp hp; exact fit A Z f V X (xQ) (A.cave x) hg (condP A x R g h hA) j
noncomputable abbrev lumG (q:Finset (Fin n)) (S:Canopy.KForm Q) (F:ℕ→ℕ):ℂ:= feek S (fun i:↥(bunch (lensR q))=> SpreadW X A x V Z F i.val) (fun i=>fPrint X A x (lensR q) i.val) -- include R auto? uses binder? inspect
#print lumG
omit R
include R
variable (hu:Injective (A.qR A.ℓ ∘ x))(hx:∀ i,X i∈ A.Ω)(hX:∀ i,(X i).material≠0)(hK:n≤ A.K)(hp:A.qR A.ℓ ∘ x∈ flats (Fin n) (2*A.e) (A.v/2))(hA:Known A)
variable (hF:Tendsto g atTop atTop)(hg:grace (D:=D) Z (φ∘g) V)(hV:∀ᶠ i in atTop,Plot P A i (Z i)) (hn:0 < n)
include hp hA hF hg hV hx hX hu hK
set_option maxHeartbeats 660000
lemma chargedM (q:Ears n): ‖lumG X A x V Z q S (φ∘g)‖≤ A.bid:=by
       let W:= tour (substr q.val); let y(i: ↥(bunch (lensR q.val))):= SpreadW X A x V Z f i.val; let l(i:↥(bunch (lensR q.val))):= fPrint X A x (lensR q.val) i.val
       have he:Available P f y l A.bid (C.S.spacing A.pA) 1:=by
            filter_upwards [(R.flows.comp hF).eventually hV] with i hi
            exact doles X A x V Z f hu hx hX hK hp W (snug _) i hi (clim (q:=q))
       refine R.here y l 1 g (fun i=>?_) hF he (fun i=> Wsettled X A x V Z R g _ hF hg hA) ((Ibis.grow ..).le) (space0 ..)
       exact rangesT X A x V Z f _ (List.nodup_ofFn.mpr (snug i.val)) hu

lemma itemized: pebG Q S (lumps X A x V Z (φ ∘ g))= CK X A x+ ∑ i∈ cutS n, again X A x i* lumG X A x V Z i S (φ∘g):=by
       let K:= lumps X A x V Z f; let w:=UI X A x V Z f; let z:=Ut X A x; let U (_: Unit) := K; let t (_:Unit) := (1:ℂ)
       have he(q:Funnel n): Strip.distinct (Plata.position (Q:=Q) (w q)):=by
            rcases q with q|q; · exact Strip.spots _|>.2 (List.nodup_nil)
            exact rangesT X A x V Z f _ (List.nodup_ofFn.mpr (snug q.snd.val)) hu
       have hS(q:Funnel n): Worn C f (w q):=by
            rcases q with q|q; · exact ⟨fun i hi=>False.elim ((List.not_mem_nil hi))⟩
            exact Wsettled X A x V Z R g _ hF hg hA
       have hL:∀ᶠ i in atTop, Klay (P:=P) U t (φ∘g) i=Klay (P:=P) w z (φ∘g) i:=by
            filter_upwards [(R.flows.comp hF).eventually hV] with i hi; have hy:∀ j V', Hom (weightsT X j) (literalK (P:=P) X A x Z ((φ ∘g) i) j V'):=by
                 intro j V'; obtain ⟨a,hp',h',hy,H'⟩:= hi.proofH n X hx hX hK (Nat.zero_lt_of_lt j.isLt) x hp; exact hy j V' 
            rw [show Klay (P:=P) U t (φ∘g) i=task P ((φ ∘g) i) (wade K i) from (by simp only[Klay,cash,Finset.univ_unique,Finset.sum_singleton,t,U,one_smul])]; exact cleft X A x V Z f hu i hy
       apply Eq.trans (b:=feek S U t) _ ((worth R U w t z g hF (fun i=>uniqueP _ _ _ _ _ _ _ hu) (fun i=>fitP _ _ _ _ _ _ _ hg (condP A x R g hF hA)) he hS hL).trans ?_); · simp [feek,U,K,t]
       unfold feek; rw [Fintype.sum_sum_type]; apply congr_arg₂ (·+·); · simp only [w,z,Compass.UI,Compass.Ut,Sum.elim_inl,Finset.univ_unique,Finset.sum_singleton]; rw [show pebG Q S []= _ from (?_ : pebG Q S []=1),mul_one]; refine Eq.trans (b:=S 0 0 0) ?_ R.blank; refine congr_arg₂ (fun y:Points 0=> fun u:Fin 0→Q.W=>S 0 y u) (Subsingleton.elim ..) (Subsingleton.elim ..)
       rw [Fintype.sum_sigma, ← sum_coe_sort (cutS n)]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold lumG feek; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _=> mul_assoc .. -- rfl
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.itemized
#print axioms YM.Intag.Sprig.Compass.chargedM
