import YM.QCD.Fold.Anch
import YM.QCD.Door.Coast
/-! # Custodial preservation of orientation of every fibre tag. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{h:f.val∣F.val}{v:Strut C}{u:Strut c}
local notation "π"=>Macrame.splitter h
variable (hr:Macrame.splitter h ∘ (act (raise G v))=(act (raise Q u)) ∘ Macrame.splitter h)
include hr
lemma submits (x y:Site F)(X:Support F)(V:Support f) (b B:ℕ):
   V∈pool h x y X b B ↔ raiseS Q u V∈ pool h (act (raise G v) x) (act (raise G v) y) (raiseS G v X) b B:= by
   let W:=act (raise G v); let Z:=act (raise Q u); let T:=({x,y}:Support F)
   have hh X: raiseS G v X=X.image W:= Finset.map_eq_image ..; have hz V: raiseS Q u V=V.image Z:=Finset.map_eq_image ..
   simp only [pool,mem_filter,mem_univ,true_and]
   have hv:Set.InjOn Z (Set.univ):= Z.injective.injOn
   have hS : {W x,W y}=T.image W:=by simp [T]
   have hT: V.image Z=raiseS Q u V:=(hz _).symm; have hE: ((raiseS G v X).image π)=(X.image π).image Z:=by rw [hh,image_image,image_image]; exact congr_arg (fun p:Site F→Site f=>X.image p) hr
   have hC : coverNumber b (raiseS Q u V)=coverNumber b V:=hz V ▸ cover_map Z (turn_sep _ _) ..
   have hA : coverNumber b (raiseS G v X)=coverNumber b X:=hh X ▸ cover_map W (turn_sep _ _) ..
   have hp (i j :Site F) (he:i=W j) : X⊆trunkFt j B ↔ (raiseS G v X)⊆trunkFt i B:= by have ht:=closeS G v B j X; rw [he]; simpa only [shortZip,mem_filter,mem_univ,true_and] using ht
   have hp' i j (he:i=W j): V⊆trunkFt (π j) B ↔ (raiseS Q u V)⊆trunkFt (π i) B:=by
      have ht := closeS Q u B (π j) V
      have hF : π i=act (raise Q u) (π j):= he.symm ▸ (show π (act (raise G v) j)=act (raise Q u) (π j) from congr_fun hr j)
      simp only [shortZip,mem_filter,mem_univ,true_and] at ht
      exact hF.symm ▸ ht
   have H i: i∈ X↔ W i ∈ raiseS G v X:=by rw [hh]; simp
   constructor
   · rintro ⟨ha,hb,hf⟩; refine ⟨hE.symm ▸ hT ▸ Finset.image_mono Z ha,hA.symm ▸ hC.symm ▸ hb,fun xH yH i hi =>?_⟩
     obtain ⟨j,hj,e⟩:= mem_image.mp (show i∈ T.image W from hS ▸ hi); exact (hp i j e.symm).symm.trans ((hf ((H _).2 xH) ((H _).2 yH) j hj).trans (hp' i j e.symm)) -- syntax
   rintro ⟨ha,hb,hf⟩; rw [hE,← hT] at ha; exact ⟨(image_subset_image_iff Z.injective).mp ha,hA ▸ hC ▸ hb,fun he hz i hi=> (hp (W i) i rfl).trans ((hf ((H x).1 he) ((H y).1 hz) (W i) ((hS).symm ▸ (mem_image_of_mem W (show i∈ T from hi)))).trans (hp' (W i) i rfl).symm)⟩
lemma flips (x y:Site F)(X:Support F)(V:Support f) (b B:ℕ):
   loan h x y X b B V=loan h (act (raise G v) x) (act (raise G v) y) (raiseS G v X) b B (raiseS Q u V):=by
   let A:= pool h x y X b B; let K:=raiseS Q u
   have hh : pool h (act (raise G v) x) (act (raise G v) y) (raiseS G v X) b B=A.image K:=by
      ext i; obtain ⟨j,rfl⟩:= K.surjective i
      simp only [mem_image, EmbeddingLike.apply_eq_iff_eq, exists_eq_right]
      exact (submits hr x y _ _ b B).symm
   have hhA : (#(pool h x y X b B))= (#(pool h (act (raise G v) x) (act (raise G v) y) (raiseS G v X) b B)):=by rw [hh]; exact (card_image_of_injective _ K.injective).symm
   simp only [loan, submits hr x y X V b B,hhA]
variable {I J:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
omit hr
lemma chargedH {p:Ratio c f}{g:I→Site f}(G:Therm I p g)(V:Land f I I)(hv:∀ (u : Strut c)(r:Site f→ℂ)(T:Spike)(X: Grid f), Warrant (raise p u) r T→∀ i j S,V i j S (settled (sky (raise p u) X))= lightP (raise p u) T r (g i)*V (G.shiftP u i) (G.shiftP u j) (raiseS p u S) (settled X)*star (lightP (raise p u) T r (g j))): Held p G G V:=by
   constructor; intro u r t hv' X x y S; obtain ⟨x,rfl⟩:= (G.shiftP u).surjective x; obtain ⟨y,rfl⟩:= (G.shiftP u).surjective y; obtain ⟨R,rfl⟩:= (raiseS p u).surjective S
   simp only [driveD, tips,Equiv.symm_apply_apply,still,hv _ _ _ X hv']; rw [← mul_assoc,← mul_assoc,(license hv' _).1,one_mul,mul_assoc,(license hv' _).1,mul_one]
lemma ranked {U:Equiv.Perm I}{V:Equiv.Perm J}{p:J→I}(he: ∀ i,p (V i)=U (p i))(x:I){E:Type*} [AddCommMonoid E](q:J→E): (∑ i∈parcel p (U x), q i)= ∑ i∈parcel p x,q (V i):=by
   rw [show parcel p (U x)=(parcel p x).image V from ?_,Finset.sum_image (V.injective.injOn)]
   ext i; obtain ⟨i,rfl⟩:=V.surjective i; simp [posted,he]
end YM.QCD.Folding
#print axioms YM.QCD.Folding.flips
