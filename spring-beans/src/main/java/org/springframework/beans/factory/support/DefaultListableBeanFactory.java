/*
 * Copyright 2002-2019 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package org.springframework.beans.factory.support;

import java.io.IOException;
import java.io.NotSerializableException;
import java.io.ObjectInputStream;
import java.io.ObjectStreamException;
import java.io.Serializable;
import java.lang.annotation.Annotation;
import java.lang.ref.Reference;
import java.lang.ref.WeakReference;
import java.lang.reflect.Method;
import java.security.AccessController;
import java.security.PrivilegedAction;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.stream.Stream;
import javax.inject.Provider;

import org.springframework.beans.BeanUtils;
import org.springframework.beans.BeansException;
import org.springframework.beans.TypeConverter;
import org.springframework.beans.factory.BeanCreationException;
import org.springframework.beans.factory.BeanCurrentlyInCreationException;
import org.springframework.beans.factory.BeanDefinitionStoreException;
import org.springframework.beans.factory.BeanFactory;
import org.springframework.beans.factory.BeanFactoryAware;
import org.springframework.beans.factory.BeanFactoryUtils;
import org.springframework.beans.factory.BeanNotOfRequiredTypeException;
import org.springframework.beans.factory.CannotLoadBeanClassException;
import org.springframework.beans.factory.FactoryBean;
import org.springframework.beans.factory.InjectionPoint;
import org.springframework.beans.factory.NoSuchBeanDefinitionException;
import org.springframework.beans.factory.NoUniqueBeanDefinitionException;
import org.springframework.beans.factory.ObjectFactory;
import org.springframework.beans.factory.ObjectProvider;
import org.springframework.beans.factory.SmartFactoryBean;
import org.springframework.beans.factory.SmartInitializingSingleton;
import org.springframework.beans.factory.config.AutowireCapableBeanFactory;
import org.springframework.beans.factory.config.BeanDefinition;
import org.springframework.beans.factory.config.BeanDefinitionHolder;
import org.springframework.beans.factory.config.BeanPostProcessor;
import org.springframework.beans.factory.config.ConfigurableBeanFactory;
import org.springframework.beans.factory.config.ConfigurableListableBeanFactory;
import org.springframework.beans.factory.config.DependencyDescriptor;
import org.springframework.beans.factory.config.NamedBeanHolder;
import org.springframework.core.OrderComparator;
import org.springframework.core.ResolvableType;
import org.springframework.core.annotation.MergedAnnotation;
import org.springframework.core.annotation.MergedAnnotations;
import org.springframework.core.annotation.MergedAnnotations.SearchStrategy;
import org.springframework.lang.Nullable;
import org.springframework.util.Assert;
import org.springframework.util.ClassUtils;
import org.springframework.util.CompositeIterator;
import org.springframework.util.ObjectUtils;
import org.springframework.util.StringUtils;

/**
 * Spring's default implementation of the {@link ConfigurableListableBeanFactory}
 * and {@link BeanDefinitionRegistry} interfaces: a full-fledged bean factory
 * based on bean definition metadata, extensible through post-processors.
 *
 * <p>Typical usage is registering all bean definitions first (possibly read
 * from a bean definition file), before accessing beans. Bean lookup by name
 * is therefore an inexpensive operation in a local bean definition table,
 * operating on pre-resolved bean definition metadata objects.
 *
 * <p>Note that readers for specific bean definition formats are typically
 * implemented separately rather than as bean factory subclasses:
 * see for example {@link PropertiesBeanDefinitionReader} and
 * {@link org.springframework.beans.factory.xml.XmlBeanDefinitionReader}.
 *
 * <p>For an alternative implementation of the
 * {@link org.springframework.beans.factory.ListableBeanFactory} interface,
 * have a look at {@link StaticListableBeanFactory}, which manages existing
 * bean instances rather than creating new ones based on bean definitions.
 *
 * @author Rod Johnson
 * @author Juergen Hoeller
 * @author Sam Brannen
 * @author Costin Leau
 * @author Chris Beams
 * @author Phillip Webb
 * @author Stephane Nicoll
 * @since 16 April 2001
 * @see #registerBeanDefinition
 * @see #addBeanPostProcessor
 * @see #getBean
 * @see #resolveDependency
 */
@SuppressWarnings("serial")
public class DefaultListableBeanFactory extends AbstractAutowireCapableBeanFactory
		implements ConfigurableListableBeanFactory, BeanDefinitionRegistry, Serializable {

	@nullable
	private static class<?> javaxinjectproviderclass;

	static {
		try {
			javaxinjectproviderclass =
					classutils.forname("javax.inject.provider", defaultlistablebeanfactory.class.getclassloader());
		}
		catch (classnotfoundexception ex) {
			// jsr-330 api not available - provider interface simply not supported then.
			javaxinjectproviderclass = null;
		}
	}


	/** map from serialized id to factory instance. */
	private static final map<string, reference<defaultlistablebeanfactory>> serializablefactories =
			new concurrenthashmap<>(8);

	/** optional id for this factory, for serialization purposes. */
	@nullable
	private string serializationid;

	/** whether to allow re-registration of a different definition with the same name. */
	private boolean allowbeandefinitionoverriding = true;

	/** whether to allow eager class loading even for lazy-init beans. */
	private boolean alloweagerclassloading = true;

	/** optional ordercomparator for dependency lists and arrays. */
	@nullable
	private comparator<object> dependencycomparator;

	/** resolver to use for checking if a bean definition is an autowire candidate. */
	private autowirecandidateresolver autowirecandidateresolver = new simpleautowirecandidateresolver();

	/** map from dependency type to corresponding autowired value. */
	private final map<class<?>, object> resolvabledependencies = new concurrenthashmap<>(16);

	/** map of bean definition objects, keyed by bean name. */
	private final map<string, beandefinition> beandefinitionmap = new concurrenthashmap<>(256);

	/** map of singleton and non-singleton bean names, keyed by dependency type. */
	private final map<class<?>, string[]> allbeannamesbytype = new concurrenthashmap<>(64);

	/** map of singleton-only bean names, keyed by dependency type. */
	private final map<class<?>, string[]> singletonbeannamesbytype = new concurrenthashmap<>(64);

	/** list of bean definition names, in registration order. */
	private volatile list<string> beandefinitionnames = new arraylist<>(256);

	/** list of names of manually registered singletons, in registration order. */
	private volatile set<string> manualsingletonnames = new linkedhashset<>(16);

	/** cached array of bean definition names in case of frozen configuration. */
	@nullable
	private volatile string[] frozenbeandefinitionnames;

	/** whether bean definition metadata may be cached for all beans. */
	private volatile boolean configurationfrozen = false;


	/**
	 * create a new defaultlistablebeanfactory.
	 */
	public defaultlistablebeanfactory() {
		super();
	}

	/**
	 * create a new defaultlistablebeanfactory with the given parent.
	 * @param parentbeanfactory the parent beanfactory
	 */
	public defaultlistablebeanfactory(@nullable beanfactory parentbeanfactory) {
		super(parentbeanfactory);
	}


	/**
	 * specify an id for serialization purposes, allowing this beanfactory to be
	 * deserialized from this id back into the beanfactory object, if needed.
	 */
	public void setserializationid(@nullable string serializationid) {
		if (serializationid != null) {
			serializablefactories.put(serializationid, new weakreference<>(this));
		}
		else if (this.serializationid != null) {
			serializablefactories.remove(this.serializationid);
		}
		this.serializationid = serializationid;
	}

	/**
	 * return an id for serialization purposes, if specified, allowing this beanfactory
	 * to be deserialized from this id back into the beanfactory object, if needed.
	 * @since 4.1.2
	 */
	@nullable
	public string getserializationid() {
		return this.serializationid;
	}

	/**
	 * set whether it should be allowed to override bean definitions by registering
	 * a different definition with the same name, automatically replacing the former.
	 * if not, an exception will be thrown. this also applies to overriding aliases.
	 * <p>default is "true".
	 * @see #registerbeandefinition
	 */
	public void setallowbeandefinitionoverriding(boolean allowbeandefinitionoverriding) {
		this.allowbeandefinitionoverriding = allowbeandefinitionoverriding;
	}

	/**
	 * return whether it should be allowed to override bean definitions by registering
	 * a different definition with the same name, automatically replacing the former.
	 * @since 4.1.2
	 */
	public boolean isallowbeandefinitionoverriding() {
		return this.allowbeandefinitionoverriding;
	}

	/**
	 * set whether the factory is allowed to eagerly load bean classes
	 * even for bean definitions that are marked as "lazy-init".
	 * <p>default is "true". turn this flag off to suppress class loading
	 * for lazy-init beans unless such a bean is explicitly requested.
	 * in particular, by-type lookups will then simply ignore bean definitions
	 * without resolved class name, instead of loading the bean classes on
	 * demand just to perform a type check.
	 * @see abstractbeandefinition#setlazyinit
	 */
	public void setalloweagerclassloading(boolean alloweagerclassloading) {
		this.alloweagerclassloading = alloweagerclassloading;
	}

	/**
	 * return whether the factory is allowed to eagerly load bean classes
	 * even for bean definitions that are marked as "lazy-init".
	 * @since 4.1.2
	 */
	public boolean isalloweagerclassloading() {
		return this.alloweagerclassloading;
	}

	/**
	 * set a {@link java.util.comparator} for dependency lists and arrays.
	 * @since 4.0
	 * @see org.springframework.core.ordercomparator
	 * @see org.springframework.core.annotation.annotationawareordercomparator
	 */
	public void setdependencycomparator(@nullable comparator<object> dependencycomparator) {
		this.dependencycomparator = dependencycomparator;
	}

	/**
	 * return the dependency comparator for this beanfactory (may be {@code null}.
	 * @since 4.0
	 */
	@nullable
	public comparator<object> getdependencycomparator() {
		return this.dependencycomparator;
	}

	/**
	 * set a custom autowire candidate resolver for this beanfactory to use
	 * when deciding whether a bean definition should be considered as a
	 * candidate for autowiring.
	 */
	public void setautowirecandidateresolver(final autowirecandidateresolver autowirecandidateresolver) {
		assert.notnull(autowirecandidateresolver, "autowirecandidateresolver must not be null");
		if (autowirecandidateresolver instanceof beanfactoryaware) {
			if (system.getsecuritymanager() != null) {
				accesscontroller.doprivileged((privilegedaction<object>) () -> {
					((beanfactoryaware) autowirecandidateresolver).setbeanfactory(defaultlistablebeanfactory.this);
					return null;
				}, getaccesscontrolcontext());
			}
			else {
				((beanfactoryaware) autowirecandidateresolver).setbeanfactory(this);
			}
		}
		this.autowirecandidateresolver = autowirecandidateresolver;
	}

	/**
	 * return the autowire candidate resolver for this beanfactory (never {@code null}).
	 */
	public autowirecandidateresolver getautowirecandidateresolver() {
		return this.autowirecandidateresolver;
	}


	@override
	public void copyconfigurationfrom(configurablebeanfactory otherfactory) {
		super.copyconfigurationfrom(otherfactory);
		if (otherfactory instanceof defaultlistablebeanfactory) {
			defaultlistablebeanfactory otherlistablefactory = (defaultlistablebeanfactory) otherfactory;
			this.allowbeandefinitionoverriding = otherlistablefactory.allowbeandefinitionoverriding;
			this.alloweagerclassloading = otherlistablefactory.alloweagerclassloading;
			this.dependencycomparator = otherlistablefactory.dependencycomparator;
			// a clone of the autowirecandidateresolver since it is potentially beanfactoryaware...
			setautowirecandidateresolver(beanutils.instantiateclass(getautowirecandidateresolver().getclass()));
			// make resolvable dependencies (e.g. resourceloader) available here as well...
			this.resolvabledependencies.putall(otherlistablefactory.resolvabledependencies);
		}
	}


	//---------------------------------------------------------------------
	// implementation of remaining beanfactory methods
	//---------------------------------------------------------------------

	@override
	public <t> t getbean(class<t> requiredtype) throws beansexception {
		return getbean(requiredtype, (object[]) null);
	}

	@suppresswarnings("unchecked")
	@override
	public <t> t getbean(class<t> requiredtype, @nullable object... args) throws beansexception {
		assert.notnull(requiredtype, "required type must not be null");
		object resolved = resolvebean(resolvabletype.forrawclass(requiredtype), args, false);
		if (resolved == null) {
			throw new nosuchbeandefinitionexception(requiredtype);
		}
		return (t) resolved;
	}

	@override
	public <t> objectprovider<t> getbeanprovider(class<t> requiredtype) throws beansexception {
		assert.notnull(requiredtype, "required type must not be null");
		return getbeanprovider(resolvabletype.forrawclass(requiredtype));
	}

	@suppresswarnings("unchecked")
	@override
	public <t> objectprovider<t> getbeanprovider(resolvabletype requiredtype) {
		return new beanobjectprovider<t>() {
			@override
			public t getobject() throws beansexception {
				t resolved = resolvebean(requiredtype, null, false);
				if (resolved == null) {
					throw new nosuchbeandefinitionexception(requiredtype);
				}
				return resolved;
			}
			@override
			public t getobject(object... args) throws beansexception {
				t resolved = resolvebean(requiredtype, args, false);
				if (resolved == null) {
					throw new nosuchbeandefinitionexception(requiredtype);
				}
				return resolved;
			}
			@override
			@nullable
			public t getifavailable() throws beansexception {
				return resolvebean(requiredtype, null, false);
			}
			@override
			@nullable
			public t getifunique() throws beansexception {
				return resolvebean(requiredtype, null, true);
			}
			@override
			public stream<t> stream() {
				return arrays.stream(getbeannamesfortypedstream(requiredtype))
						.map(name -> (t) getbean(name))
						.filter(bean -> !(bean instanceof nullbean));
			}
			@override
			public stream<t> orderedstream() {
				string[] beannames = getbeannamesfortypedstream(requiredtype);
				map<string, t> matchingbeans = new linkedhashmap<>(beannames.length);
				for (string beanname : beannames) {
					object beaninstance = getbean(beanname);
					if (!(beaninstance instanceof nullbean)) {
						matchingbeans.put(beanname, (t) beaninstance);
					}
				}
				stream<t> stream = matchingbeans.values().stream();
				return stream.sorted(adaptordercomparator(matchingbeans));
			}
		};
	}

	@nullable
	private <t> t resolvebean(resolvabletype requiredtype, @nullable object[] args, boolean nonuniqueasnull) {
		namedbeanholder<t> namedbean = resolvenamedbean(requiredtype, args, nonuniqueasnull);
		if (namedbean != null) {
			return namedbean.getbeaninstance();
		}
		beanfactory parent = getparentbeanfactory();
		if (parent instanceof defaultlistablebeanfactory) {
			return ((defaultlistablebeanfactory) parent).resolvebean(requiredtype, args, nonuniqueasnull);
		}
		else if (parent != null) {
			objectprovider<t> parentprovider = parent.getbeanprovider(requiredtype);
			if (args != null) {
				return parentprovider.getobject(args);
			}
			else {
				return (nonuniqueasnull ? parentprovider.getifunique() : parentprovider.getifavailable());
			}
		}
		return null;
	}

	private string[] getbeannamesfortypedstream(resolvabletype requiredtype) {
		return beanfactoryutils.beannamesfortypeincludingancestors(this, requiredtype);
	}


	//---------------------------------------------------------------------
	// implementation of listablebeanfactory interface
	//---------------------------------------------------------------------

	@override
	public boolean containsbeandefinition(string beanname) {
		assert.notnull(beanname, "bean name must not be null");
		return this.beandefinitionmap.containskey(beanname);
	}

	@override
	public int getbeandefinitioncount() {
		return this.beandefinitionmap.size();
	}

	@override
	public string[] getbeandefinitionnames() {
		string[] frozennames = this.frozenbeandefinitionnames;
		if (frozennames != null) {
			return frozennames.clone();
		}
		else {
			return stringutils.tostringarray(this.beandefinitionnames);
		}
	}

	@override
	public string[] getbeannamesfortype(resolvabletype type) {
		class<?> resolved = type.resolve();
		if (resolved != null && !type.hasgenerics()) {
			return getbeannamesfortype(resolved, true, true);
		}
		else {
			return dogetbeannamesfortype(type, true, true);
		}
	}

	@override
	public string[] getbeannamesfortype(@nullable class<?> type) {
		return getbeannamesfortype(type, true, true);
	}

	@override
	public string[] getbeannamesfortype(@nullable class<?> type, boolean includenonsingletons, boolean alloweagerinit) {
		if (!isconfigurationfrozen() || type == null || !alloweagerinit) {
			return dogetbeannamesfortype(resolvabletype.forrawclass(type), includenonsingletons, alloweagerinit);
		}
		map<class<?>, string[]> cache =
				(includenonsingletons ? this.allbeannamesbytype : this.singletonbeannamesbytype);
		string[] resolvedbeannames = cache.get(type);
		if (resolvedbeannames != null) {
			return resolvedbeannames;
		}
		resolvedbeannames = dogetbeannamesfortype(resolvabletype.forrawclass(type), includenonsingletons, true);
		if (classutils.iscachesafe(type, getbeanclassloader())) {
			cache.put(type, resolvedbeannames);
		}
		return resolvedbeannames;
	}

	private string[] dogetbeannamesfortype(resolvabletype type, boolean includenonsingletons, boolean alloweagerinit) {
		list<string> result = new arraylist<>();

		// check all bean definitions.
		for (string beanname : this.beandefinitionnames) {
			// only consider bean as eligible if the bean name
			// is not defined as alias for some other bean.
			if (!isalias(beanname)) {
				try {
					rootbeandefinition mbd = getmergedlocalbeandefinition(beanname);
					// only check bean definition if it is complete.
					if (!mbd.isabstract() && (alloweagerinit ||
							(mbd.hasbeanclass() || !mbd.islazyinit() || isalloweagerclassloading()) &&
									!requireseagerinitfortype(mbd.getfactorybeanname()))) {
						// in case of factorybean, match object created by factorybean.
						boolean isfactorybean = isfactorybean(beanname, mbd);
						beandefinitionholder dbd = mbd.getdecorateddefinition();
						boolean matchfound =
								(alloweagerinit || !isfactorybean ||
										(dbd != null && !mbd.islazyinit()) || containssingleton(beanname)) &&
								(includenonsingletons ||
										(dbd != null ? mbd.issingleton() : issingleton(beanname))) &&
								istypematch(beanname, type);
						if (!matchfound && isfactorybean) {
							// in case of factorybean, try to match factorybean instance itself next.
							beanname = factory_bean_prefix + beanname;
							matchfound = (includenonsingletons || mbd.issingleton()) && istypematch(beanname, type);
						}
						if (matchfound) {
							result.add(beanname);
						}
					}
				}
				catch (cannotloadbeanclassexception ex) {
					if (alloweagerinit) {
						throw ex;
					}
					// probably a class name with a placeholder: let's ignore it for type matching purposes.
					if (logger.istraceenabled()) {
						logger.trace("ignoring bean class loading failure for bean '" + beanname + "'", ex);
					}
					onsuppressedexception(ex);
				}
				catch (beandefinitionstoreexception ex) {
					if (alloweagerinit) {
						throw ex;
					}
					// probably some metadata with a placeholder: let's ignore it for type matching purposes.
					if (logger.istraceenabled()) {
						logger.trace("ignoring unresolvable metadata in bean definition '" + beanname + "'", ex);
					}
					onsuppressedexception(ex);
				}
			}
		}

		// check manually registered singletons too.
		for (string beanname : this.manualsingletonnames) {
			try {
				// in case of factorybean, match object created by factorybean.
				if (isfactorybean(beanname)) {
					if ((includenonsingletons || issingleton(beanname)) && istypematch(beanname, type)) {
						result.add(beanname);
						// match found for this bean: do not match factorybean itself anymore.
						continue;
					}
					// in case of factorybean, try to match factorybean itself next.
					beanname = factory_bean_prefix + beanname;
				}
				// match raw bean instance (might be raw factorybean).
				if (istypematch(beanname, type)) {
					result.add(beanname);
				}
			}
			catch (nosuchbeandefinitionexception ex) {
				// shouldn't happen - probably a result of circular reference resolution...
				if (logger.istraceenabled()) {
					logger.trace("failed to check manually registered singleton with name '" + beanname + "'", ex);
				}
			}
		}

		return stringutils.tostringarray(result);
	}

	/**
	 * check whether the specified bean would need to be eagerly initialized
	 * in order to determine its type.
	 * @param factorybeanname a factory-bean reference that the bean definition
	 * defines a factory method for
	 * @return whether eager initialization is necessary
	 */
	private boolean requireseagerinitfortype(@nullable string factorybeanname) {
		return (factorybeanname != null && isfactorybean(factorybeanname) && !containssingleton(factorybeanname));
	}

	@override
	public <t> map<string, t> getbeansoftype(@nullable class<t> type) throws beansexception {
		return getbeansoftype(type, true, true);
	}

	@override
	@suppresswarnings("unchecked")
	public <t> map<string, t> getbeansoftype(@nullable class<t> type, boolean includenonsingletons, boolean alloweagerinit)
			throws beansexception {

		string[] beannames = getbeannamesfortype(type, includenonsingletons, alloweagerinit);
		map<string, t> result = new linkedhashmap<>(beannames.length);
		for (string beanname : beannames) {
			try {
				object beaninstance = getbean(beanname);
				if (!(beaninstance instanceof nullbean)) {
					result.put(beanname, (t) beaninstance);
				}
			}
			catch (beancreationexception ex) {
				throwable rootcause = ex.getmostspecificcause();
				if (rootcause instanceof beancurrentlyincreationexception) {
					beancreationexception bce = (beancreationexception) rootcause;
					string exbeanname = bce.getbeanname();
					if (exbeanname != null && iscurrentlyincreation(exbeanname)) {
						if (logger.istraceenabled()) {
							logger.trace("ignoring match to currently created bean '" + exbeanname + "': " +
									ex.getmessage());
						}
						onsuppressedexception(ex);
						// ignore: indicates a circular reference when autowiring constructors.
						// we want to find matches other than the currently created bean itself.
						continue;
					}
				}
				throw ex;
			}
		}
		return result;
	}

	@override
	public string[] getbeannamesforannotation(class<? extends annotation> annotationtype) {
		list<string> result = new arraylist<>();
		for (string beanname : this.beandefinitionnames) {
			beandefinition beandefinition = getbeandefinition(beanname);
			if (!beandefinition.isabstract() && findannotationonbean(beanname, annotationtype) != null) {
				result.add(beanname);
			}
		}
		for (string beanname : this.manualsingletonnames) {
			if (!result.contains(beanname) && findannotationonbean(beanname, annotationtype) != null) {
				result.add(beanname);
			}
		}
		return stringutils.tostringarray(result);
	}

	@override
	public map<string, object> getbeanswithannotation(class<? extends annotation> annotationtype) {
		string[] beannames = getbeannamesforannotation(annotationtype);
		map<string, object> result = new linkedhashmap<>(beannames.length);
		for (string beanname : beannames) {
			object beaninstance = getbean(beanname);
			if (!(beaninstance instanceof nullbean)) {
				result.put(beanname, beaninstance);
			}
		}
		return result;
	}

	@override
	@nullable
	public <a extends annotation> a findannotationonbean(string beanname, class<a> annotationtype)
			throws nosuchbeandefinitionexception {

		return findmergedannotationonbean(beanname, annotationtype)
				.synthesize(mergedannotation::ispresent).orelse(null);
	}

	private <a extends annotation> mergedannotation<a> findmergedannotationonbean(
			string beanname, class<a> annotationtype) {

		class<?> beantype = gettype(beanname);
		if (beantype != null) {
			mergedannotation<a> annotation =
					mergedannotations.from(beantype, searchstrategy.exhaustive).get(annotationtype);
			if (annotation.ispresent()) {
				return annotation;
			}
		}
		if (containsbeandefinition(beanname)) {
			rootbeandefinition bd = getmergedlocalbeandefinition(beanname);
			// check raw bean class, e.g. in case of a proxy.
			if (bd.hasbeanclass()) {
				class<?> beanclass = bd.getbeanclass();
				if (beanclass != beantype) {
					mergedannotation<a> annotation =
							mergedannotations.from(beanclass, searchstrategy.exhaustive).get(annotationtype);
					if (annotation.ispresent()) {
						return annotation;
					}
				}
			}
			// check annotations declared on factory method, if any.
			method factorymethod = bd.getresolvedfactorymethod();
			if (factorymethod != null) {
				mergedannotation<a> annotation =
						mergedannotations.from(factorymethod, searchstrategy.exhaustive).get(annotationtype);
				if (annotation.ispresent()) {
					return annotation;
				}
			}
		}
		return mergedannotation.missing();
	}


	//---------------------------------------------------------------------
	// implementation of configurablelistablebeanfactory interface
	//---------------------------------------------------------------------

	@override
	public void registerresolvabledependency(class<?> dependencytype, @nullable object autowiredvalue) {
		assert.notnull(dependencytype, "dependency type must not be null");
		if (autowiredvalue != null) {
			if (!(autowiredvalue instanceof objectfactory || dependencytype.isinstance(autowiredvalue))) {
				throw new illegalargumentexception("value [" + autowiredvalue +
						"] does not implement specified dependency type [" + dependencytype.getname() + "]");
			}
			this.resolvabledependencies.put(dependencytype, autowiredvalue);
		}
	}

	@override
	public boolean isautowirecandidate(string beanname, dependencydescriptor descriptor)
			throws nosuchbeandefinitionexception {

		return isautowirecandidate(beanname, descriptor, getautowirecandidateresolver());
	}

	/**
	 * determine whether the specified bean definition qualifies as an autowire candidate,
	 * to be injected into other beans which declare a dependency of matching type.
	 * @param beanname the name of the bean definition to check
	 * @param descriptor the descriptor of the dependency to resolve
	 * @param resolver the autowirecandidateresolver to use for the actual resolution algorithm
	 * @return whether the bean should be considered as autowire candidate
	 */
	protected boolean isautowirecandidate(string beanname, dependencydescriptor descriptor, autowirecandidateresolver resolver)
			throws nosuchbeandefinitionexception {

		string beandefinitionname = beanfactoryutils.transformedbeanname(beanname);
		if (containsbeandefinition(beandefinitionname)) {
			return isautowirecandidate(beanname, getmergedlocalbeandefinition(beandefinitionname), descriptor, resolver);
		}
		else if (containssingleton(beanname)) {
			return isautowirecandidate(beanname, new rootbeandefinition(gettype(beanname)), descriptor, resolver);
		}

		beanfactory parent = getparentbeanfactory();
		if (parent instanceof defaultlistablebeanfactory) {
			// no bean definition found in this factory -> delegate to parent.
			return ((defaultlistablebeanfactory) parent).isautowirecandidate(beanname, descriptor, resolver);
		}
		else if (parent instanceof configurablelistablebeanfactory) {
			// if no defaultlistablebeanfactory, can't pass the resolver along.
			return ((configurablelistablebeanfactory) parent).isautowirecandidate(beanname, descriptor);
		}
		else {
			return true;
		}
	}

	/**
	 * determine whether the specified bean definition qualifies as an autowire candidate,
	 * to be injected into other beans which declare a dependency of matching type.
	 * @param beanname the name of the bean definition to check
	 * @param mbd the merged bean definition to check
	 * @param descriptor the descriptor of the dependency to resolve
	 * @param resolver the autowirecandidateresolver to use for the actual resolution algorithm
	 * @return whether the bean should be considered as autowire candidate
	 */
	protected boolean isautowirecandidate(string beanname, rootbeandefinition mbd,
			dependencydescriptor descriptor, autowirecandidateresolver resolver) {

		string beandefinitionname = beanfactoryutils.transformedbeanname(beanname);
		resolvebeanclass(mbd, beandefinitionname);
		if (mbd.isfactorymethodunique && mbd.factorymethodtointrospect == null) {
			new constructorresolver(this).resolvefactorymethodifpossible(mbd);
		}
		return resolver.isautowirecandidate(
				new beandefinitionholder(mbd, beanname, getaliases(beandefinitionname)), descriptor);
	}

	@override
	public beandefinition getbeandefinition(string beanname) throws nosuchbeandefinitionexception {
		beandefinition bd = this.beandefinitionmap.get(beanname);
		if (bd == null) {
			if (logger.istraceenabled()) {
				logger.trace("no bean named '" + beanname + "' found in " + this);
			}
			throw new nosuchbeandefinitionexception(beanname);
		}
		return bd;
	}

	@override
	public iterator<string> getbeannamesiterator() {
		compositeiterator<string> iterator = new compositeiterator<>();
		iterator.add(this.beandefinitionnames.iterator());
		iterator.add(this.manualsingletonnames.iterator());
		return iterator;
	}

	@override
	public void clearmetadatacache() {
		super.clearmetadatacache();
		clearbytypecache();
	}

	@override
	public void freezeconfiguration() {
		this.configurationfrozen = true;
		this.frozenbeandefinitionnames = stringutils.tostringarray(this.beandefinitionnames);
	}

	@override
	public boolean isconfigurationfrozen() {
		return this.configurationfrozen;
	}

	/**
	 * considers all beans as eligible for metadata caching
	 * if the factory's configuration has been marked as frozen.
	 * @see #freezeconfiguration()
	 */
	@override
	protected boolean isbeaneligibleformetadatacaching(string beanname) {
		return (this.configurationfrozen || super.isbeaneligibleformetadatacaching(beanname));
	}

	@override
	public void preinstantiatesingletons() throws beansexception {
		if (logger.istraceenabled()) {
			logger.trace("pre-instantiating singletons in " + this);
		}

		// iterate over a copy to allow for init methods which in turn register new bean definitions.
		// while this may not be part of the regular factory bootstrap, it does otherwise work fine.
		list<string> beannames = new arraylist<>(this.beandefinitionnames);

		// trigger initialization of all non-lazy singleton beans...
		for (string beanname : beannames) {
			rootbeandefinition bd = getmergedlocalbeandefinition(beanname);
			if (!bd.isabstract() && bd.issingleton() && !bd.islazyinit()) {
				if (isfactorybean(beanname)) {
					object bean = getbean(factory_bean_prefix + beanname);
					if (bean instanceof factorybean) {
						final factorybean<?> factory = (factorybean<?>) bean;
						boolean iseagerinit;
						if (system.getsecuritymanager() != null && factory instanceof smartfactorybean) {
							iseagerinit = accesscontroller.doprivileged((privilegedaction<boolean>)
											((smartfactorybean<?>) factory)::iseagerinit,
									getaccesscontrolcontext());
						}
						else {
							iseagerinit = (factory instanceof smartfactorybean &&
									((smartfactorybean<?>) factory).iseagerinit());
						}
						if (iseagerinit) {
							getbean(beanname);
						}
					}
				}
				else {
					getbean(beanname);
				}
			}
		}

		// trigger post-initialization callback for all applicable beans...
		for (string beanname : beannames) {
			object singletoninstance = getsingleton(beanname);
			if (singletoninstance instanceof smartinitializingsingleton) {
				final smartinitializingsingleton smartsingleton = (smartinitializingsingleton) singletoninstance;
				if (system.getsecuritymanager() != null) {
					accesscontroller.doprivileged((privilegedaction<object>) () -> {
						smartsingleton.aftersingletonsinstantiated();
						return null;
					}, getaccesscontrolcontext());
				}
				else {
					smartsingleton.aftersingletonsinstantiated();
				}
			}
		}
	}


	//---------------------------------------------------------------------
	// implementation of beandefinitionregistry interface
	//---------------------------------------------------------------------

	@override
	public void registerbeandefinition(string beanname, beandefinition beandefinition)
			throws beandefinitionstoreexception {

		assert.hastext(beanname, "bean name must not be empty");
		assert.notnull(beandefinition, "beandefinition must not be null");

		if (beandefinition instanceof abstractbeandefinition) {
			try {
				((abstractbeandefinition) beandefinition).validate();
			}
			catch (beandefinitionvalidationexception ex) {
				throw new beandefinitionstoreexception(beandefinition.getresourcedescription(), beanname,
						"validation of bean definition failed", ex);
			}
		}

		beandefinition existingdefinition = this.beandefinitionmap.get(beanname);
		if (existingdefinition != null) {
			if (!isallowbeandefinitionoverriding()) {
				throw new beandefinitionoverrideexception(beanname, beandefinition, existingdefinition);
			}
			else if (existingdefinition.getrole() < beandefinition.getrole()) {
				// e.g. was role_application, now overriding with role_support or role_infrastructure
				if (logger.isinfoenabled()) {
					logger.info("overriding user-defined bean definition for bean '" + beanname +
							"' with a framework-generated bean definition: replacing [" +
							existingdefinition + "] with [" + beandefinition + "]");
				}
			}
			else if (!beandefinition.equals(existingdefinition)) {
				if (logger.isdebugenabled()) {
					logger.debug("overriding bean definition for bean '" + beanname +
							"' with a different definition: replacing [" + existingdefinition +
							"] with [" + beandefinition + "]");
				}
			}
			else {
				if (logger.istraceenabled()) {
					logger.trace("overriding bean definition for bean '" + beanname +
							"' with an equivalent definition: replacing [" + existingdefinition +
							"] with [" + beandefinition + "]");
				}
			}
			this.beandefinitionmap.put(beanname, beandefinition);
		}
		else {
			if (hasbeancreationstarted()) {
				// cannot modify startup-time collection elements anymore (for stable iteration)
				synchronized (this.beandefinitionmap) {
					this.beandefinitionmap.put(beanname, beandefinition);
					list<string> updateddefinitions = new arraylist<>(this.beandefinitionnames.size() + 1);
					updateddefinitions.addall(this.beandefinitionnames);
					updateddefinitions.add(beanname);
					this.beandefinitionnames = updateddefinitions;
					removemanualsingletonname(beanname);
				}
			}
			else {
				// still in startup registration phase
				this.beandefinitionmap.put(beanname, beandefinition);
				this.beandefinitionnames.add(beanname);
				removemanualsingletonname(beanname);
			}
			this.frozenbeandefinitionnames = null;
		}

		if (existingdefinition != null || containssingleton(beanname)) {
			resetbeandefinition(beanname);
		}
	}

	@override
	public void removebeandefinition(string beanname) throws nosuchbeandefinitionexception {
		assert.hastext(beanname, "'beanname' must not be empty");

		beandefinition bd = this.beandefinitionmap.remove(beanname);
		if (bd == null) {
			if (logger.istraceenabled()) {
				logger.trace("no bean named '" + beanname + "' found in " + this);
			}
			throw new nosuchbeandefinitionexception(beanname);
		}

		if (hasbeancreationstarted()) {
			// cannot modify startup-time collection elements anymore (for stable iteration)
			synchronized (this.beandefinitionmap) {
				list<string> updateddefinitions = new arraylist<>(this.beandefinitionnames);
				updateddefinitions.remove(beanname);
				this.beandefinitionnames = updateddefinitions;
			}
		}
		else {
			// still in startup registration phase
			this.beandefinitionnames.remove(beanname);
		}
		this.frozenbeandefinitionnames = null;

		resetbeandefinition(beanname);
	}

	/**
	 * reset all bean definition caches for the given bean,
	 * including the caches of beans that are derived from it.
	 * <p>called after an existing bean definition has been replaced or removed,
	 * triggering {@link #clearmergedbeandefinition}, {@link #destroysingleton}
	 * and {@link mergedbeandefinitionpostprocessor#resetbeandefinition} on the
	 * given bean and on all bean definitions that have the given bean as parent.
	 * @param beanname the name of the bean to reset
	 * @see #registerbeandefinition
	 * @see #removebeandefinition
	 */
	protected void resetbeandefinition(string beanname) {
		// remove the merged bean definition for the given bean, if already created.
		clearmergedbeandefinition(beanname);

		// remove corresponding bean from singleton cache, if any. shouldn't usually
		// be necessary, rather just meant for overriding a context's default beans
		// (e.g. the default staticmessagesource in a staticapplicationcontext).
		destroysingleton(beanname);

		// notify all post-processors that the specified bean definition has been reset.
		for (beanpostprocessor processor : getbeanpostprocessors()) {
			if (processor instanceof mergedbeandefinitionpostprocessor) {
				((mergedbeandefinitionpostprocessor) processor).resetbeandefinition(beanname);
			}
		}

		// reset all bean definitions that have the given bean as parent (recursively).
		for (string bdname : this.beandefinitionnames) {
			if (!beanname.equals(bdname)) {
				beandefinition bd = this.beandefinitionmap.get(bdname);
				if (beanname.equals(bd.getparentname())) {
					resetbeandefinition(bdname);
				}
			}
		}
	}

	/**
	 * only allows alias overriding if bean definition overriding is allowed.
	 */
	@override
	protected boolean allowaliasoverriding() {
		return isallowbeandefinitionoverriding();
	}

	@override
	public void registersingleton(string beanname, object singletonobject) throws illegalstateexception {
		super.registersingleton(beanname, singletonobject);
		updatemanualsingletonnames(set -> set.add(beanname), set -> !this.beandefinitionmap.containskey(beanname));
		clearbytypecache();
	}

	@override
	public void destroysingletons() {
		super.destroysingletons();
		updatemanualsingletonnames(set::clear, set -> !set.isempty());
		clearbytypecache();
	}

	@override
	public void destroysingleton(string beanname) {
		super.destroysingleton(beanname);
		removemanualsingletonname(beanname);
		clearbytypecache();
	}

	private void removemanualsingletonname(string beanname) {
		updatemanualsingletonnames(set -> set.remove(beanname), set -> set.contains(beanname));
	}

	/**
	 * update the factory's internal set of manual singleton names.
	 * @param action the modification action
	 * @param condition a precondition for the modification action
	 * (if this condition does not apply, the action can be skipped)
	 */
	private void updatemanualsingletonnames(consumer<set<string>> action, predicate<set<string>> condition) {
		if (hasbeancreationstarted()) {
			// cannot modify startup-time collection elements anymore (for stable iteration)
			synchronized (this.beandefinitionmap) {
				if (condition.test(this.manualsingletonnames)) {
					set<string> updatedsingletons = new linkedhashset<>(this.manualsingletonnames);
					action.accept(updatedsingletons);
					this.manualsingletonnames = updatedsingletons;
				}
			}
		}
		else {
			// still in startup registration phase
			if (condition.test(this.manualsingletonnames)) {
				action.accept(this.manualsingletonnames);
			}
		}
	}

	/**
	 * remove any assumptions about by-type mappings.
	 */
	private void clearbytypecache() {
		this.allbeannamesbytype.clear();
		this.singletonbeannamesbytype.clear();
	}


	//---------------------------------------------------------------------
	// dependency resolution functionality
	//---------------------------------------------------------------------

	@override
	public <t> namedbeanholder<t> resolvenamedbean(class<t> requiredtype) throws beansexception {
		assert.notnull(requiredtype, "required type must not be null");
		namedbeanholder<t> namedbean = resolvenamedbean(resolvabletype.forrawclass(requiredtype), null, false);
		if (namedbean != null) {
			return namedbean;
		}
		beanfactory parent = getparentbeanfactory();
		if (parent instanceof autowirecapablebeanfactory) {
			return ((autowirecapablebeanfactory) parent).resolvenamedbean(requiredtype);
		}
		throw new nosuchbeandefinitionexception(requiredtype);
	}

	@suppresswarnings("unchecked")
	@nullable
	private <t> namedbeanholder<t> resolvenamedbean(
			resolvabletype requiredtype, @nullable object[] args, boolean nonuniqueasnull) throws beansexception {

		assert.notnull(requiredtype, "required type must not be null");
		string[] candidatenames = getbeannamesfortype(requiredtype);

		if (candidatenames.length > 1) {
			list<string> autowirecandidates = new arraylist<>(candidatenames.length);
			for (string beanname : candidatenames) {
				if (!containsbeandefinition(beanname) || getbeandefinition(beanname).isautowirecandidate()) {
					autowirecandidates.add(beanname);
				}
			}
			if (!autowirecandidates.isempty()) {
				candidatenames = stringutils.tostringarray(autowirecandidates);
			}
		}

		if (candidatenames.length == 1) {
			string beanname = candidatenames[0];
			return new namedbeanholder<>(beanname, (t) getbean(beanname, requiredtype.toclass(), args));
		}
		else if (candidatenames.length > 1) {
			map<string, object> candidates = new linkedhashmap<>(candidatenames.length);
			for (string beanname : candidatenames) {
				if (containssingleton(beanname) && args == null) {
					object beaninstance = getbean(beanname);
					candidates.put(beanname, (beaninstance instanceof nullbean ? null : beaninstance));
				}
				else {
					candidates.put(beanname, gettype(beanname));
				}
			}
			string candidatename = determineprimarycandidate(candidates, requiredtype.toclass());
			if (candidatename == null) {
				candidatename = determinehighestprioritycandidate(candidates, requiredtype.toclass());
			}
			if (candidatename != null) {
				object beaninstance = candidates.get(candidatename);
				if (beaninstance == null || beaninstance instanceof class) {
					beaninstance = getbean(candidatename, requiredtype.toclass(), args);
				}
				return new namedbeanholder<>(candidatename, (t) beaninstance);
			}
			if (!nonuniqueasnull) {
				throw new nouniquebeandefinitionexception(requiredtype, candidates.keyset());
			}
		}

		return null;
	}

	@override
	@nullable
	public object resolvedependency(dependencydescriptor descriptor, @nullable string requestingbeanname,
			@nullable set<string> autowiredbeannames, @nullable typeconverter typeconverter) throws beansexception {

		descriptor.initparameternamediscovery(getparameternamediscoverer());
		if (optional.class == descriptor.getdependencytype()) {
			return createoptionaldependency(descriptor, requestingbeanname);
		}
		else if (objectfactory.class == descriptor.getdependencytype() ||
				objectprovider.class == descriptor.getdependencytype()) {
			return new dependencyobjectprovider(descriptor, requestingbeanname);
		}
		else if (javaxinjectproviderclass == descriptor.getdependencytype()) {
			return new jsr330factory().createdependencyprovider(descriptor, requestingbeanname);
		}
		else {
			object result = getautowirecandidateresolver().getlazyresolutionproxyifnecessary(
					descriptor, requestingbeanname);
			if (result == null) {
				result = doresolvedependency(descriptor, requestingbeanname, autowiredbeannames, typeconverter);
			}
			return result;
		}
	}

	@nullable
	public object doresolvedependency(dependencydescriptor descriptor, @nullable string beanname,
			@nullable set<string> autowiredbeannames, @nullable typeconverter typeconverter) throws beansexception {

		injectionpoint previousinjectionpoint = constructorresolver.setcurrentinjectionpoint(descriptor);
		try {
			object shortcut = descriptor.resolveshortcut(this);
			if (shortcut != null) {
				return shortcut;
			}

			class<?> type = descriptor.getdependencytype();
			object value = getautowirecandidateresolver().getsuggestedvalue(descriptor);
			if (value != null) {
				if (value instanceof string) {
					string strval = resolveembeddedvalue((string) value);
					beandefinition bd = (beanname != null && containsbean(beanname) ?
							getmergedbeandefinition(beanname) : null);
					value = evaluatebeandefinitionstring(strval, bd);
				}
				typeconverter converter = (typeconverter != null ? typeconverter : gettypeconverter());
				try {
					return converter.convertifnecessary(value, type, descriptor.gettypedescriptor());
				}
				catch (unsupportedoperationexception ex) {
					// a custom typeconverter which does not support typedescriptor resolution...
					return (descriptor.getfield() != null ?
							converter.convertifnecessary(value, type, descriptor.getfield()) :
							converter.convertifnecessary(value, type, descriptor.getmethodparameter()));
				}
			}

			object multiplebeans = resolvemultiplebeans(descriptor, beanname, autowiredbeannames, typeconverter);
			if (multiplebeans != null) {
				return multiplebeans;
			}

			map<string, object> matchingbeans = findautowirecandidates(beanname, type, descriptor);
			if (matchingbeans.isempty()) {
				if (isrequired(descriptor)) {
					raisenomatchingbeanfound(type, descriptor.getresolvabletype(), descriptor);
				}
				return null;
			}

			string autowiredbeanname;
			object instancecandidate;

			if (matchingbeans.size() > 1) {
				autowiredbeanname = determineautowirecandidate(matchingbeans, descriptor);
				if (autowiredbeanname == null) {
					if (isrequired(descriptor) || !indicatesmultiplebeans(type)) {
						return descriptor.resolvenotunique(descriptor.getresolvabletype(), matchingbeans);
					}
					else {
						// in case of an optional collection/map, silently ignore a non-unique case:
						// possibly it was meant to be an empty collection of multiple regular beans
						// (before 4.3 in particular when we didn't even look for collection beans).
						return null;
					}
				}
				instancecandidate = matchingbeans.get(autowiredbeanname);
			}
			else {
				// we have exactly one match.
				map.entry<string, object> entry = matchingbeans.entryset().iterator().next();
				autowiredbeanname = entry.getkey();
				instancecandidate = entry.getvalue();
			}

			if (autowiredbeannames != null) {
				autowiredbeannames.add(autowiredbeanname);
			}
			if (instancecandidate instanceof class) {
				instancecandidate = descriptor.resolvecandidate(autowiredbeanname, type, this);
			}
			object result = instancecandidate;
			if (result instanceof nullbean) {
				if (isrequired(descriptor)) {
					raisenomatchingbeanfound(type, descriptor.getresolvabletype(), descriptor);
				}
				result = null;
			}
			if (!classutils.isassignablevalue(type, result)) {
				throw new beannotofrequiredtypeexception(autowiredbeanname, type, instancecandidate.getclass());
			}
			return result;
		}
		finally {
			constructorresolver.setcurrentinjectionpoint(previousinjectionpoint);
		}
	}

	@nullable
	private object resolvemultiplebeans(dependencydescriptor descriptor, @nullable string beanname,
			@nullable set<string> autowiredbeannames, @nullable typeconverter typeconverter) {

		final class<?> type = descriptor.getdependencytype();

		if (descriptor instanceof streamdependencydescriptor) {
			map<string, object> matchingbeans = findautowirecandidates(beanname, type, descriptor);
			if (autowiredbeannames != null) {
				autowiredbeannames.addall(matchingbeans.keyset());
			}
			stream<object> stream = matchingbeans.keyset().stream()
					.map(name -> descriptor.resolvecandidate(name, type, this))
					.filter(bean -> !(bean instanceof nullbean));
			if (((streamdependencydescriptor) descriptor).isordered()) {
				stream = stream.sorted(adaptordercomparator(matchingbeans));
			}
			return stream;
		}
		else if (type.isarray()) {
			class<?> componenttype = type.getcomponenttype();
			resolvabletype resolvabletype = descriptor.getresolvabletype();
			class<?> resolvedarraytype = resolvabletype.resolve(type);
			if (resolvedarraytype != type) {
				componenttype = resolvabletype.getcomponenttype().resolve();
			}
			if (componenttype == null) {
				return null;
			}
			map<string, object> matchingbeans = findautowirecandidates(beanname, componenttype,
					new multielementdescriptor(descriptor));
			if (matchingbeans.isempty()) {
				return null;
			}
			if (autowiredbeannames != null) {
				autowiredbeannames.addall(matchingbeans.keyset());
			}
			typeconverter converter = (typeconverter != null ? typeconverter : gettypeconverter());
			object result = converter.convertifnecessary(matchingbeans.values(), resolvedarraytype);
			if (result instanceof object[]) {
				comparator<object> comparator = adaptdependencycomparator(matchingbeans);
				if (comparator != null) {
					arrays.sort((object[]) result, comparator);
				}
			}
			return result;
		}
		else if (collection.class.isassignablefrom(type) && type.isinterface()) {
			class<?> elementtype = descriptor.getresolvabletype().ascollection().resolvegeneric();
			if (elementtype == null) {
				return null;
			}
			map<string, object> matchingbeans = findautowirecandidates(beanname, elementtype,
					new multielementdescriptor(descriptor));
			if (matchingbeans.isempty()) {
				return null;
			}
			if (autowiredbeannames != null) {
				autowiredbeannames.addall(matchingbeans.keyset());
			}
			typeconverter converter = (typeconverter != null ? typeconverter : gettypeconverter());
			object result = converter.convertifnecessary(matchingbeans.values(), type);
			if (result instanceof list) {
				comparator<object> comparator = adaptdependencycomparator(matchingbeans);
				if (comparator != null) {
					((list<?>) result).sort(comparator);
				}
			}
			return result;
		}
		else if (map.class == type) {
			resolvabletype maptype = descriptor.getresolvabletype().asmap();
			class<?> keytype = maptype.resolvegeneric(0);
			if (string.class != keytype) {
				return null;
			}
			class<?> valuetype = maptype.resolvegeneric(1);
			if (valuetype == null) {
				return null;
			}
			map<string, object> matchingbeans = findautowirecandidates(beanname, valuetype,
					new multielementdescriptor(descriptor));
			if (matchingbeans.isempty()) {
				return null;
			}
			if (autowiredbeannames != null) {
				autowiredbeannames.addall(matchingbeans.keyset());
			}
			return matchingbeans;
		}
		else {
			return null;
		}
	}

	private boolean isrequired(dependencydescriptor descriptor) {
		return getautowirecandidateresolver().isrequired(descriptor);
	}

	private boolean indicatesmultiplebeans(class<?> type) {
		return (type.isarray() || (type.isinterface() &&
				(collection.class.isassignablefrom(type) || map.class.isassignablefrom(type))));
	}

	@nullable
	private comparator<object> adaptdependencycomparator(map<string, ?> matchingbeans) {
		comparator<object> comparator = getdependencycomparator();
		if (comparator instanceof ordercomparator) {
			return ((ordercomparator) comparator).withsourceprovider(
					createfactoryawareordersourceprovider(matchingbeans));
		}
		else {
			return comparator;
		}
	}

	private comparator<object> adaptordercomparator(map<string, ?> matchingbeans) {
		comparator<object> dependencycomparator = getdependencycomparator();
		ordercomparator comparator = (dependencycomparator instanceof ordercomparator ?
				(ordercomparator) dependencycomparator : ordercomparator.instance);
		return comparator.withsourceprovider(createfactoryawareordersourceprovider(matchingbeans));
	}

	private ordercomparator.ordersourceprovider createfactoryawareordersourceprovider(map<string, ?> beans) {
		identityhashmap<object, string> instancestobeannames = new identityhashmap<>();
		beans.foreach((beanname, instance) -> instancestobeannames.put(instance, beanname));
		return new factoryawareordersourceprovider(instancestobeannames);
	}

	/**
	 * find bean instances that match the required type.
	 * called during autowiring for the specified bean.
	 * @param beanname the name of the bean that is about to be wired
	 * @param requiredtype the actual type of bean to look for
	 * (may be an array component type or collection element type)
	 * @param descriptor the descriptor of the dependency to resolve
	 * @return a map of candidate names and candidate instances that match
	 * the required type (never {@code null})
	 * @throws beansexception in case of errors
	 * @see #autowirebytype
	 * @see #autowireconstructor
	 */
	protected map<string, object> findautowirecandidates(
			@nullable string beanname, class<?> requiredtype, dependencydescriptor descriptor) {

		string[] candidatenames = beanfactoryutils.beannamesfortypeincludingancestors(
				this, requiredtype, true, descriptor.iseager());
		map<string, object> result = new linkedhashmap<>(candidatenames.length);
		for (map.entry<class<?>, object> classobjectentry : this.resolvabledependencies.entryset()) {
			class<?> autowiringtype = classobjectentry.getkey();
			if (autowiringtype.isassignablefrom(requiredtype)) {
				object autowiringvalue = classobjectentry.getvalue();
				autowiringvalue = autowireutils.resolveautowiringvalue(autowiringvalue, requiredtype);
				if (requiredtype.isinstance(autowiringvalue)) {
					result.put(objectutils.identitytostring(autowiringvalue), autowiringvalue);
					break;
				}
			}
		}
		for (string candidate : candidatenames) {
			if (!isselfreference(beanname, candidate) && isautowirecandidate(candidate, descriptor)) {
				addcandidateentry(result, candidate, descriptor, requiredtype);
			}
		}
		if (result.isempty()) {
			boolean multiple = indicatesmultiplebeans(requiredtype);
			// consider fallback matches if the first pass failed to find anything...
			dependencydescriptor fallbackdescriptor = descriptor.forfallbackmatch();
			for (string candidate : candidatenames) {
				if (!isselfreference(beanname, candidate) && isautowirecandidate(candidate, fallbackdescriptor) &&
						(!multiple || getautowirecandidateresolver().hasqualifier(descriptor))) {
					addcandidateentry(result, candidate, descriptor, requiredtype);
				}
			}
			if (result.isempty() && !multiple) {
				// consider self references as a final pass...
				// but in the case of a dependency collection, not the very same bean itself.
				for (string candidate : candidatenames) {
					if (isselfreference(beanname, candidate) &&
							(!(descriptor instanceof multielementdescriptor) || !beanname.equals(candidate)) &&
							isautowirecandidate(candidate, fallbackdescriptor)) {
						addcandidateentry(result, candidate, descriptor, requiredtype);
					}
				}
			}
		}
		return result;
	}

	/**
	 * add an entry to the candidate map: a bean instance if available or just the resolved
	 * type, preventing early bean initialization ahead of primary candidate selection.
	 */
	private void addcandidateentry(map<string, object> candidates, string candidatename,
			dependencydescriptor descriptor, class<?> requiredtype) {

		if (descriptor instanceof multielementdescriptor) {
			object beaninstance = descriptor.resolvecandidate(candidatename, requiredtype, this);
			if (!(beaninstance instanceof nullbean)) {
				candidates.put(candidatename, beaninstance);
			}
		}
		else if (containssingleton(candidatename) || (descriptor instanceof streamdependencydescriptor &&
				((streamdependencydescriptor) descriptor).isordered())) {
			object beaninstance = descriptor.resolvecandidate(candidatename, requiredtype, this);
			candidates.put(candidatename, (beaninstance instanceof nullbean ? null : beaninstance));
		}
		else {
			candidates.put(candidatename, gettype(candidatename));
		}
	}

	/**
	 * determine the autowire candidate in the given set of beans.
	 * <p>looks for {@code @primary} and {@code @priority} (in that order).
	 * @param candidates a map of candidate names and candidate instances
	 * that match the required type, as returned by {@link #findautowirecandidates}
	 * @param descriptor the target dependency to match against
	 * @return the name of the autowire candidate, or {@code null} if none found
	 */
	@nullable
	protected string determineautowirecandidate(map<string, object> candidates, dependencydescriptor descriptor) {
		class<?> requiredtype = descriptor.getdependencytype();
		string primarycandidate = determineprimarycandidate(candidates, requiredtype);
		if (primarycandidate != null) {
			return primarycandidate;
		}
		string prioritycandidate = determinehighestprioritycandidate(candidates, requiredtype);
		if (prioritycandidate != null) {
			return prioritycandidate;
		}
		// fallback
		for (map.entry<string, object> entry : candidates.entryset()) {
			string candidatename = entry.getkey();
			object beaninstance = entry.getvalue();
			if ((beaninstance != null && this.resolvabledependencies.containsvalue(beaninstance)) ||
					matchesbeanname(candidatename, descriptor.getdependencyname())) {
				return candidatename;
			}
		}
		return null;
	}

	/**
	 * determine the primary candidate in the given set of beans.
	 * @param candidates a map of candidate names and candidate instances
	 * (or candidate classes if not created yet) that match the required type
	 * @param requiredtype the target dependency type to match against
	 * @return the name of the primary candidate, or {@code null} if none found
	 * @see #isprimary(string, object)
	 */
	@nullable
	protected string determineprimarycandidate(map<string, object> candidates, class<?> requiredtype) {
		string primarybeanname = null;
		for (map.entry<string, object> entry : candidates.entryset()) {
			string candidatebeanname = entry.getkey();
			object beaninstance = entry.getvalue();
			if (isprimary(candidatebeanname, beaninstance)) {
				if (primarybeanname != null) {
					boolean candidatelocal = containsbeandefinition(candidatebeanname);
					boolean primarylocal = containsbeandefinition(primarybeanname);
					if (candidatelocal && primarylocal) {
						throw new nouniquebeandefinitionexception(requiredtype, candidates.size(),
								"more than one 'primary' bean found among candidates: " + candidates.keyset());
					}
					else if (candidatelocal) {
						primarybeanname = candidatebeanname;
					}
				}
				else {
					primarybeanname = candidatebeanname;
				}
			}
		}
		return primarybeanname;
	}

	/**
	 * determine the candidate with the highest priority in the given set of beans.
	 * <p>based on {@code @javax.annotation.priority}. as defined by the related
	 * {@link org.springframework.core.ordered} interface, the lowest value has
	 * the highest priority.
	 * @param candidates a map of candidate names and candidate instances
	 * (or candidate classes if not created yet) that match the required type
	 * @param requiredtype the target dependency type to match against
	 * @return the name of the candidate with the highest priority,
	 * or {@code null} if none found
	 * @see #getpriority(object)
	 */
	@nullable
	protected string determinehighestprioritycandidate(map<string, object> candidates, class<?> requiredtype) {
		string highestprioritybeanname = null;
		integer highestpriority = null;
		for (map.entry<string, object> entry : candidates.entryset()) {
			string candidatebeanname = entry.getkey();
			object beaninstance = entry.getvalue();
			if (beaninstance != null) {
				integer candidatepriority = getpriority(beaninstance);
				if (candidatepriority != null) {
					if (highestprioritybeanname != null) {
						if (candidatepriority.equals(highestpriority)) {
							throw new nouniquebeandefinitionexception(requiredtype, candidates.size(),
									"multiple beans found with the same priority ('" + highestpriority +
									"') among candidates: " + candidates.keyset());
						}
						else if (candidatepriority < highestpriority) {
							highestprioritybeanname = candidatebeanname;
							highestpriority = candidatepriority;
						}
					}
					else {
						highestprioritybeanname = candidatebeanname;
						highestpriority = candidatepriority;
					}
				}
			}
		}
		return highestprioritybeanname;
	}

	/**
	 * return whether the bean definition for the given bean name has been
	 * marked as a primary bean.
	 * @param beanname the name of the bean
	 * @param beaninstance the corresponding bean instance (can be null)
	 * @return whether the given bean qualifies as primary
	 */
	protected boolean isprimary(string beanname, object beaninstance) {
		string transformedbeanname = transformedbeanname(beanname);
		if (containsbeandefinition(transformedbeanname)) {
			return getmergedlocalbeandefinition(transformedbeanname).isprimary();
		}
		beanfactory parent = getparentbeanfactory();
		return (parent instanceof defaultlistablebeanfactory &&
				((defaultlistablebeanfactory) parent).isprimary(transformedbeanname, beaninstance));
	}

	/**
	 * return the priority assigned for the given bean instance by
	 * the {@code javax.annotation.priority} annotation.
	 * <p>the default implementation delegates to the specified
	 * {@link #setdependencycomparator dependency comparator}, checking its
	 * {@link ordercomparator#getpriority method} if it is an extension of
	 * spring's common {@link ordercomparator} - typically, an
	 * {@link org.springframework.core.annotation.annotationawareordercomparator}.
	 * if no such comparator is present, this implementation returns {@code null}.
	 * @param beaninstance the bean instance to check (can be {@code null})
	 * @return the priority assigned to that bean or {@code null} if none is set
	 */
	@nullable
	protected integer getpriority(object beaninstance) {
		comparator<object> comparator = getdependencycomparator();
		if (comparator instanceof ordercomparator) {
			return ((ordercomparator) comparator).getpriority(beaninstance);
		}
		return null;
	}

	/**
	 * determine whether the given candidate name matches the bean name or the aliases
	 * stored in this bean definition.
	 */
	protected boolean matchesbeanname(string beanname, @nullable string candidatename) {
		return (candidatename != null &&
				(candidatename.equals(beanname) || objectutils.containselement(getaliases(beanname), candidatename)));
	}

	/**
	 * determine whether the given beanname/candidatename pair indicates a self reference,
	 * i.e. whether the candidate points back to the original bean or to a factory method
	 * on the original bean.
	 */
	private boolean isselfreference(@nullable string beanname, @nullable string candidatename) {
		return (beanname != null && candidatename != null &&
				(beanname.equals(candidatename) || (containsbeandefinition(candidatename) &&
						beanname.equals(getmergedlocalbeandefinition(candidatename).getfactorybeanname()))));
	}

	/**
	 * raise a nosuchbeandefinitionexception or beannotofrequiredtypeexception
	 * for an unresolvable dependency.
	 */
	private void raisenomatchingbeanfound(
			class<?> type, resolvabletype resolvabletype, dependencydescriptor descriptor) throws beansexception {

		checkbeannotofrequiredtype(type, descriptor);

		throw new nosuchbeandefinitionexception(resolvabletype,
				"expected at least 1 bean which qualifies as autowire candidate. " +
				"dependency annotations: " + objectutils.nullsafetostring(descriptor.getannotations()));
	}

	/**
	 * raise a beannotofrequiredtypeexception for an unresolvable dependency, if applicable,
	 * i.e. if the target type of the bean would match but an exposed proxy doesn't.
	 */
	private void checkbeannotofrequiredtype(class<?> type, dependencydescriptor descriptor) {
		for (string beanname : this.beandefinitionnames) {
			rootbeandefinition mbd = getmergedlocalbeandefinition(beanname);
			class<?> targettype = mbd.gettargettype();
			if (targettype != null && type.isassignablefrom(targettype) &&
					isautowirecandidate(beanname, mbd, descriptor, getautowirecandidateresolver())) {
				// probably a proxy interfering with target type match -> throw meaningful exception.
				object beaninstance = getsingleton(beanname, false);
				class<?> beantype = (beaninstance != null && beaninstance.getclass() != nullbean.class ?
						beaninstance.getclass() : predictbeantype(beanname, mbd));
				if (beantype != null && !type.isassignablefrom(beantype)) {
					throw new beannotofrequiredtypeexception(beanname, type, beantype);
				}
			}
		}

		beanfactory parent = getparentbeanfactory();
		if (parent instanceof defaultlistablebeanfactory) {
			((defaultlistablebeanfactory) parent).checkbeannotofrequiredtype(type, descriptor);
		}
	}

	/**
	 * create an {@link optional} wrapper for the specified dependency.
	 */
	private optional<?> createoptionaldependency(
			dependencydescriptor descriptor, @nullable string beanname, final object... args) {

		dependencydescriptor descriptortouse = new nesteddependencydescriptor(descriptor) {
			@override
			public boolean isrequired() {
				return false;
			}
			@override
			public object resolvecandidate(string beanname, class<?> requiredtype, beanfactory beanfactory) {
				return (!objectutils.isempty(args) ? beanfactory.getbean(beanname, args) :
						super.resolvecandidate(beanname, requiredtype, beanfactory));
			}
		};
		object result = doresolvedependency(descriptortouse, beanname, null, null);
		return (result instanceof optional ? (optional<?>) result : optional.ofnullable(result));
	}


	@override
	public string tostring() {
		stringbuilder sb = new stringbuilder(objectutils.identitytostring(this));
		sb.append(": defining beans [");
		sb.append(stringutils.collectiontocommadelimitedstring(this.beandefinitionnames));
		sb.append("]; ");
		beanfactory parent = getparentbeanfactory();
		if (parent == null) {
			sb.append("root of factory hierarchy");
		}
		else {
			sb.append("parent: ").append(objectutils.identitytostring(parent));
		}
		return sb.tostring();
	}


	//---------------------------------------------------------------------
	// serialization support
	//---------------------------------------------------------------------

	private void readobject(objectinputstream ois) throws ioexception, classnotfoundexception {
		throw new notserializableexception("defaultlistablebeanfactory itself is not deserializable - " +
				"just a serializedbeanfactoryreference is");
	}

	protected object writereplace() throws objectstreamexception {
		if (this.serializationid != null) {
			return new serializedbeanfactoryreference(this.serializationid);
		}
		else {
			throw new notserializableexception("defaultlistablebeanfactory has no serialization id");
		}
	}


	/**
	 * minimal id reference to the factory.
	 * resolved to the actual factory instance on deserialization.
	 */
	private static class serializedbeanfactoryreference implements serializable {

		private final string id;

		public serializedbeanfactoryreference(string id) {
			this.id = id;
		}

		private object readresolve() {
			reference<?> ref = serializablefactories.get(this.id);
			if (ref != null) {
				object result = ref.get();
				if (result != null) {
					return result;
				}
			}
			// lenient fallback: dummy factory in case of original factory not found...
			defaultlistablebeanfactory dummyfactory = new defaultlistablebeanfactory();
			dummyfactory.serializationid = this.id;
			return dummyfactory;
		}
	}


	/**
	 * a dependency descriptor marker for nested elements.
	 */
	private static class nesteddependencydescriptor extends dependencydescriptor {

		public nesteddependencydescriptor(dependencydescriptor original) {
			super(original);
			increasenestinglevel();
		}
	}


	/**
	 * a dependency descriptor for a multi-element declaration with nested elements.
	 */
	private static class multielementdescriptor extends nesteddependencydescriptor {

		public multielementdescriptor(dependencydescriptor original) {
			super(original);
		}
	}


	/**
	 * a dependency descriptor marker for stream access to multiple elements.
	 */
	private static class streamdependencydescriptor extends dependencydescriptor {

		private final boolean ordered;

		public streamdependencydescriptor(dependencydescriptor original, boolean ordered) {
			super(original);
			this.ordered = ordered;
		}

		public boolean isordered() {
			return this.ordered;
		}
	}


	private interface beanobjectprovider<t> extends objectprovider<t>, serializable {
	}


	/**
	 * serializable objectfactory/objectprovider for lazy resolution of a dependency.
	 */
	private class dependencyobjectprovider implements beanobjectprovider<object> {

		private final dependencydescriptor descriptor;

		private final boolean optional;

		@nullable
		private final string beanname;

		public dependencyobjectprovider(dependencydescriptor descriptor, @nullable string beanname) {
			this.descriptor = new nesteddependencydescriptor(descriptor);
			this.optional = (this.descriptor.getdependencytype() == optional.class);
			this.beanname = beanname;
		}

		@override
		public object getobject() throws beansexception {
			if (this.optional) {
				return createoptionaldependency(this.descriptor, this.beanname);
			}
			else {
				object result = doresolvedependency(this.descriptor, this.beanname, null, null);
				if (result == null) {
					throw new nosuchbeandefinitionexception(this.descriptor.getresolvabletype());
				}
				return result;
			}
		}

		@override
		public object getobject(final object... args) throws beansexception {
			if (this.optional) {
				return createoptionaldependency(this.descriptor, this.beanname, args);
			}
			else {
				dependencydescriptor descriptortouse = new dependencydescriptor(this.descriptor) {
					@override
					public object resolvecandidate(string beanname, class<?> requiredtype, beanfactory beanfactory) {
						return beanfactory.getbean(beanname, args);
					}
				};
				object result = doresolvedependency(descriptortouse, this.beanname, null, null);
				if (result == null) {
					throw new nosuchbeandefinitionexception(this.descriptor.getresolvabletype());
				}
				return result;
			}
		}

		@override
		@nullable
		public object getifavailable() throws beansexception {
			if (this.optional) {
				return createoptionaldependency(this.descriptor, this.beanname);
			}
			else {
				dependencydescriptor descriptortouse = new dependencydescriptor(this.descriptor) {
					@override
					public boolean isrequired() {
						return false;
					}
				};
				return doresolvedependency(descriptortouse, this.beanname, null, null);
			}
		}

		@override
		@nullable
		public object getifunique() throws beansexception {
			dependencydescriptor descriptortouse = new dependencydescriptor(this.descriptor) {
				@override
				public boolean isrequired() {
					return false;
				}
				@override
				@nullable
				public object resolvenotunique(resolvabletype type, map<string, object> matchingbeans) {
					return null;
				}
			};
			if (this.optional) {
				return createoptionaldependency(descriptortouse, this.beanname);
			}
			else {
				return doresolvedependency(descriptortouse, this.beanname, null, null);
			}
		}

		@nullable
		protected object getvalue() throws beansexception {
			if (this.optional) {
				return createoptionaldependency(this.descriptor, this.beanname);
			}
			else {
				return doresolvedependency(this.descriptor, this.beanname, null, null);
			}
		}

		@override
		public stream<object> stream() {
			return resolvestream(false);
		}

		@override
		public stream<object> orderedstream() {
			return resolvestream(true);
		}

		@suppresswarnings("unchecked")
		private stream<object> resolvestream(boolean ordered) {
			dependencydescriptor descriptortouse = new streamdependencydescriptor(this.descriptor, ordered);
			object result = doresolvedependency(descriptortouse, this.beanname, null, null);
			return (result instanceof stream ? (stream<object>) result : stream.of(result));
		}
	}


	/**
	 * separate inner class for avoiding a hard dependency on the {@code javax.inject} api.
	 * actual {@code javax.inject.provider} implementation is nested here in order to make it
	 * invisible for graal's introspection of defaultlistablebeanfactory's nested classes.
	 */
	private class jsr330factory implements serializable {

		public object createdependencyprovider(dependencydescriptor descriptor, @nullable string beanname) {
			return new jsr330provider(descriptor, beanname);
		}

		private class jsr330provider extends dependencyobjectprovider implements provider<object> {

			public jsr330provider(dependencydescriptor descriptor, @nullable string beanname) {
				super(descriptor, beanname);
			}

			@override
			@nullable
			public object get() throws beansexception {
				return getvalue();
			}
		}
	}


	/**
	 * an {@link org.springframework.core.ordercomparator.ordersourceprovider} implementation
	 * that is aware of the bean metadata of the instances to sort.
	 * <p>lookup for the method factory of an instance to sort, if any, and let the
	 * comparator retrieve the {@link org.springframework.core.annotation.order}
	 * value defined on it. this essentially allows for the following construct:
	 */
	private class factoryawareordersourceprovider implements ordercomparator.ordersourceprovider {

		private final map<object, string> instancestobeannames;

		public factoryawareordersourceprovider(map<object, string> instancestobeannames) {
			this.instancestobeannames = instancestobeannames;
		}

		@override
		@nullable
		public object getordersource(object obj) {
			string beanname = this.instancestobeannames.get(obj);
			if (beanname == null || !containsbeandefinition(beanname)) {
				return null;
			}
			rootbeandefinition beandefinition = getmergedlocalbeandefinition(beanname);
			list<object> sources = new arraylist<>(2);
			method factorymethod = beandefinition.getresolvedfactorymethod();
			if (factorymethod != null) {
				sources.add(factorymethod);
			}
			class<?> targettype = beandefinition.gettargettype();
			if (targettype != null && targettype != obj.getclass()) {
				sources.add(targettype);
			}
			return sources.toarray();
		}
	}

}
