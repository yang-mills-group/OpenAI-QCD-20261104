import YM.Elms.Carpet
/-! # Witnesses in root-invariant stencil families
Flavor clocks at term ENTRY through matching at any Chamber.[rank physics still with barriers]. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
structure Knot (p: Label d) where
    X : Drape
    Y : Drape
    g : ℕ
    m : ℕ
    t : ℕ
    s : ℕ
    M : ℕ
    r : ℕ
    c {n:Side} : Regulator n 6→ ℝ
abbrev Knot.tool {p:Label d}(V:Knot p)(P:Regulator n 6) : Drape:= V.X+ ((V.c P:ℂ)) • V.Y
noncomputable abbrev levy (g m:ℕ)(t v:ℝ):ℝ:= t^g*v^m
structure Requisite (H:SourceRead.TaperHol)(p:Label d)(V:Knot p) :Prop where
    mantle : V.X∈ phrase V.g V.s
    rent : V.Y∈ phrase V.m V.t
    hasi : Profile V.X -- field notation Profile namespace Gallery.Draft use adjust
    hasy : Profile V.Y
    finance : polarity V.t=polarity V.s
    spectrum : Survey H V.X V.g V.s (passport d p)
    nullN : ∀ (n:Side)(P:Regulator n 6), P.t=0→V.M ≤ n.val→P.β ≠ 0→ ∀ o:Cover, NullOn P (V.tool P n o) (Outer V.r (wrap n o))
    cash : ∀ (n:Side)(P:Regulator n 6)(v t ε:ℝ), 0<v→0<t→0 < P.β→ v^2/(t*P.β) ≤ ε →(∀ i:Flavor 6,|P.m i|≤ ε) → |V.c P| *levy V.m V.t t v ≤ ε* levy V.g V.s t v
variable (H:SourceRead.TaperHol)(K:Hol su)
def Pivots (H:SourceRead.TaperHol)(d:ℕ): Set (Label d):={x | ∃ p:Knot x, Requisite H x p}
noncomputable def toneG (n:Side)(P:Regulator n 6): ℝ:= -P.β⁻¹
lemma fossil (i:su.ColorIndex)(l:List Bough)(h :∀ k∈l,carat k e.e)(hp:Peg K (d/2)): miniR d (glitter K e i d*canopy K d l) ∈ Pivots H d:=by
   let X:=flashF e i*leaflet l; let Y:=flashK e (ico i)*leaflet l; let z:= glitter K e i d*canopy K d l
   let p:= miniR d z; have hW:=flashing e H K i hp; have ht:=hW.mul (leaves H K l hp); rw [fold_taps] at ht
   let Q:= 1+gaugeI l; let R:=0+gaugeI l; let g:=0+fermI l; let v:=2+fermI l; have hX:X∈ phrase Q g:= pages_mul (cloak e i) (pagedB l); have hY: Y∈phrase R v:=pages_mul (glowK e i) (pagedB l)
   have h'X:=shelf hX; have h'Y:=shelf hY
   obtain ⟨M,r,hm⟩:= bentB e l i h -- binder l,i
   obtain ⟨x,h₀,hx⟩:= Civic.sheen h'X.film; obtain ⟨y,h₁,hy⟩:= Civic.sheen h'Y.film; let f0:Knot p:=⟨x,y,Q,R,v,g,M,r,fun {n}=>toneG n⟩;
   refine ⟨f0, ⟨chapZ hX hx,chapZ hY hy,profileShears _ _ _ _ hX hx,profileShears _ _ _ _ hY hy, ?_, ?_, ?_,?_⟩⟩
   · change polarity v=polarity g; rw [show v=g+2*1 from (by unfold v g; omega),pol_eq]
   · exact Civic.Shears.survey hx h'X ht
   · intro n P hT hn hb o; let c:ℂ:= (toneG _ P:ℝ); have he:=hx.add (hy.smul c); refine Civic.stillborn P he (h'X.film.addR (h'Y.film.scaleR c)) o ?_
     let f:=X+c • Y; have ht:f n o=button P o e (ico i)*leaflet l n o:=by rw [button,sub_mul, _root_.smul_mul_assoc, sub_eq_add_neg]; change X n o+c • Y n o=_+_; unfold c toneG; rw [Complex.ofReal_neg, Complex.ofReal_inv,neg_smul]; rfl
     change NullOn P (f n o) _; rw [ht]; exact hm n _ hn hT hb o
   intro n P v' t' ε hv ht hb he hf; change |toneG n P| *(levy R v t' v')≤ ε*levy Q g t' v'; unfold toneG levy Q R g v; rw [abs_neg,abs_of_pos (inv_pos.mpr hb),Nat.zero_add,Nat.zero_add,pow_add,pow_add, pow_one]; apply (le_trans _ (mul_le_mul_of_nonneg_right he (by positivity))); apply le_of_eq; field_simp -- finish
lemma spinTint (q:Bool)(i:Dike)(l:List Bough)(h:∀ k∈l,vacant k (stop 0 w))(hp: Peg K (d/2)): miniR d (flora (Grass.line (Pulses.bent q i.1.1 i.1.2 i.2 (stop 0 w)))* canopy K d l) ∈Pivots H d:=by
    let X:= brake w i q*leaflet l; let Y:= burnish w q i*leaflet l; let z:= flora (Grass.line (Pulses.bent (d:=d) q i.1.1 i.1.2 i.2 (stop 0 w)))* canopy K d l; let p:= miniR d z
    let r':=0+gaugeI l; let t:=1+fermI l; have hu:X∈phrase r' t:=pages_mul (rateSb w i q) (pagedB l); have hv:Y∈phrase r' t:=pages_mul (miniBurn q i w) (pagedB l) -- fix
    have h'X:=shelf hu; have h'Y:=shelf hv
    obtain ⟨M,r,hm⟩:= spinSilence q w i l h -- order w? due variables
    obtain ⟨x,h₀,hx⟩:= Civic.sheen h'X.film; obtain ⟨y,h₁,hy⟩:= Civic.sheen h'Y.film; let W:Knot p:=⟨x,y,r',r',t,t,M,r,fun P=> P.m i.2⟩; have ht:= (motor w H K i q d).mul (leaves H K l hp); rw [fold_taps] at ht
    refine ⟨W, ⟨chapZ hu hx,chapZ hv hy,profileShears _ _ _ _ hu hx,profileShears _ _ _ _ hv hy,rfl, Civic.Shears.survey hx h'X ht,?_,?_⟩⟩
    · intro n P hT hn hb o; let c:ℂ:=(P.m i.2:ℂ); let Z:=X+c • Y
      have he:=hx.add (hy.smul c); refine Civic.stillborn P he ?_ o ?_; swap
      · change NullOn P (Z n o) _; rw [show Z n o=solar P q o w i*leaflet l n o from ?_]; exact hm n _ hn hT o
        rw [endPulse,add_mul,add_comm]; change _=_+ _ ; rw [_root_.smul_mul_assoc]; rfl
      exact h'X.film.addR (h'Y.film.scaleR c)
    intro n P v q ε hv ht hb he hh; apply mul_le_mul_of_nonneg_right (hh i.2) (by unfold levy; positivity)
section Group
lemma afford (hp:∀ k,Peg K k) : Module.finrank ℂ (LinearMap.ker (@UV.Free.projection d)) ≤ Module.finrank ℂ (Submodule.span ℂ (Pivots H d)):=by
   let R:=Submodule.span ℂ (Pivots H d); apply budget R K hp; apply suited R K hp; constructor
   · intro w i l h; exact Submodule.subset_span (fossil w H K i l h (hp _))
   intro q i k u b l h; obtain ⟨w,he⟩:∃ w:Walk,stop (0:Cover) w=b:=⟨ route 0 b 1, route_end ..⟩; subst b; exact Submodule.subset_span (spinTint w H K q ((i,k),u) l h (hp _)) -- sig
noncomputable abbrev sizeD (d:ℕ):=Module.finrank ℂ (LinearMap.ker (@UV.Free.projection d))
lemma chosen (d:ℕ)(hp: ∀ k,Peg K k): ∃ V: Fin (sizeD d)→Label d, (∀ i,V i∈ Pivots H d)∧LinearIndependent ℂ V :=by
    apply sized _ _ (afford H K hp)
 where
    sized (A:Set (Label d))(n:ℕ)(h:n≤ Module.finrank ℂ (Submodule.span ℂ A)): ∃ V:Fin n→Label d, (∀ i,V i∈ A)∧LinearIndependent ℂ V:=by
        induction n with
        | zero=> exact ⟨fun i=>i.elim0,fun i=>i.elim0,linearIndependent_empty_type⟩
        | succ n ih=> obtain ⟨v,hv,hw⟩:=ih (Nat.le_of_lt h)
                      let R:=Submodule.span ℂ (Set.range v); obtain ⟨g,hg,hg'⟩: ∃ g∈A,g∉R:=by
                          by_contra! hh; have he:= Submodule.finrank_mono (Submodule.span_le.mpr hh); have hs: Module.finrank ℂ R=n:=by rw [show Module.finrank ℂ R=_ from finrank_span_eq_card hw]; simp
                          omega
                      exact ⟨Fin.cons g v,fun i=> Fin.cases (by simpa) (fun j=>by simpa using hv j) i, hw.finCons hg'⟩
end Group
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.chosen
