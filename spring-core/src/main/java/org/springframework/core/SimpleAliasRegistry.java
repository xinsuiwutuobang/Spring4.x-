/*
 * Copyright 2002-2018 the original author or authors.
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

package org.springframework.core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.apache.commons.logging.Log;
import org.apache.commons.logging.LogFactory;

import org.springframework.util.Assert;
import org.springframework.util.StringUtils;
import org.springframework.util.StringValueResolver;

/**
 * Simple implementation of the {@link AliasRegistry} interface.
 * Serves as base class for
 * {@link org.springframework.beans.factory.support.BeanDefinitionRegistry}
 * implementations.
 *
 * @author Juergen Hoeller
 * @since 2.5.2
 * 简单别名注册
 * SimpleAliasRegistry 为AliasRegistry的默认实现，内部使用ConcurrentHashMap作为内存注册表，
 * 存储alias-name的映射关系，同时alias-name可以循环引用如: a->b ,c->a ,d->c。
 *
 */
public class SimpleAliasRegistry implements AliasRegistry {

	/** Logger available to subclasses. */
	protected final Log logger = LogFactory.getLog(getClass());

	/** Map from alias to canonical name. */
	//别名-指定名称的映射MAP，用于存储注册信息（内存注册表）
	private final Map<String, String> aliasMap = new ConcurrentHashMap<>(16);


	@Override
	public void registerAlias(String name, String alias) {
		Assert.hasText(name, "'name' must not be empty");
		Assert.hasText(alias, "'alias' must not be empty");
		//锁注册表
		//因为CurrentHashMap只有put和remove是线程安全的
		//此处要保证对CurrentHashMap的复合操作线程安全
		synchronized (this.aliasMap) {
			//判断别名与指定名称是否一样
			if (alias.equals(name)) {
				// 一样时，在注册表移除当前别名信息
				this.aliasMap.remove(alias);
				if (logger.isDebugEnabled()) {
					logger.debug("Alias definition '" + alias + "' ignored since it points to same name");
				}
			} else {
				//获取当前别名在注册表中的指定名称
				String registeredName = this.aliasMap.get(alias);
				if (registeredName != null) {
					//指定名称存在，不需要注册，返回
					if (registeredName.equals(name)) {
						// An existing alias - no need to re-register
						return;
					}
					//判断是否允许重写注册
					if (!allowAliasOverriding()) {
						throw new IllegalStateException("Cannot define alias '" + alias + "' for name '" +
								name + "': It is already registered for name '" + registeredName + "'.");
					}
					if (logger.isDebugEnabled()) {
						logger.debug("Overriding alias '" + alias + "' definition for registered name '" +
								registeredName + "' with new target name '" + name + "'");
					}
				}
				//校验指定名称是否指向当前别名的
				checkForAliasCircle(name, alias);
				//注册表注册别名与指定名称的映射
				this.aliasMap.put(alias, name);
				if (logger.isTraceEnabled()) {
					logger.trace("Alias definition '" + alias + "' registered for name '" + name + "'");
				}
			}
		}
	}

	/**
	 * Return whether alias overriding is allowed.
	 * Default is {@code true}.
	 * 是否允许重写注册表别名信息，默认true
	 */
	protected boolean allowAliasOverriding() {
		return true;
	}

	/**
	 * Determine(确定) whether the given name has the given alias registered.
	 * @param name the name to check
	 * @param alias the alias to look for
	 * @since 4.2.1
	 * 校验给定的alias-name映射是否已在注册表aliasMap中
	 */
	public boolean hasAlias(String name, String alias) {
		// 遍历注册表
		for (Map.Entry<String, String> entry : this.aliasMap.entrySet()) {
			// 注册表中单映射的指定名称name
			String registeredName = entry.getValue();
			// 判断name是否与传入name一致
			if (registeredName.equals(name)) {
				// 获取注册表单项的别名
				String registeredAlias = entry.getKey();
				// hasAlias(registeredAlias, alias)) 检测是否存在循环引用
				// 循环引用如下
				// 注册表: A-B; C-A;D-C
				// B对应的别名有ACD
				// A对应的别名别名CD
				// C对应的别名有D
				// 是循环引用 此处需要校验
				if (registeredAlias.equals(alias) || hasAlias(registeredAlias, alias)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * 在注册表aliasMap中,移除别名
	 * @param alias the alias to remove
	 */
	@Override
	public void removeAlias(String alias) {
		synchronized (this.aliasMap) {
			String name = this.aliasMap.remove(alias);
			if (name == null) {
				throw new IllegalStateException("No alias '" + alias + "' registered");
			}
		}
	}

	/**
	 * 校验是否包含给定的别名，在注册表aliasMap中
	 * @param name the name to check
	 * @return
	 */
	@Override
	public boolean isAlias(String name) {
		return this.aliasMap.containsKey(name);
	}

	/**
	 * 在注册表获取指定名称的所有别名信息
	 * @param name the name to check for aliases
	 * @return
	 */
	@Override
	public String[] getAliases(String name) {
		List<String> result = new ArrayList<>();
		synchronized (this.aliasMap) {
			retrieveAliases(name, result);
		}
		return StringUtils.toStringArray(result);
	}

	/**
	 * Transitively retrieve（递归检索） all aliases for the given name.
	 * @param name the target name to find aliases for
	 * @param result the resulting aliases list
	 *
	 */
	private void retrieveAliases(String name, List<String> result) {
		this.aliasMap.forEach((alias, registeredName) -> {
			if (registeredName.equals(name)) {
				result.add(alias);
				retrieveAliases(alias, result);
			}
		});
	}

	/**
	 * Resolve all alias target names and aliases registered in this
	 * factory, applying the given StringValueResolver to them.
	 * <p>The value resolver may for example resolve placeholders
	 * in target bean names and even in alias names.
	 * @param valueResolver the StringValueResolver to apply
	 */
	public void resolveAliases(StringValueResolver valueResolver) {
		Assert.notNull(valueResolver, "StringValueResolver must not be null");
		synchronized (this.aliasMap) {
			Map<String, String> aliasCopy = new HashMap<>(this.aliasMap);
			aliasCopy.forEach((alias, registeredName) -> {
				String resolvedAlias = valueResolver.resolveStringValue(alias);
				String resolvedName = valueResolver.resolveStringValue(registeredName);
				if (resolvedAlias == null || resolvedName == null || resolvedAlias.equals(resolvedName)) {
					this.aliasMap.remove(alias);
				}
				else if (!resolvedAlias.equals(alias)) {
					String existingName = this.aliasMap.get(resolvedAlias);
					if (existingName != null) {
						if (existingName.equals(resolvedName)) {
							// Pointing to existing alias - just remove placeholder
							this.aliasMap.remove(alias);
							return;
						}
						throw new IllegalStateException(
								"Cannot register resolved alias '" + resolvedAlias + "' (original: '" + alias +
								"') for name '" + resolvedName + "': It is already registered for name '" +
								registeredName + "'.");
					}
					checkForAliasCircle(resolvedName, resolvedAlias);
					this.aliasMap.remove(alias);
					this.aliasMap.put(resolvedAlias, resolvedName);
				}
				else if (!registeredName.equals(resolvedName)) {
					this.aliasMap.put(alias, resolvedName);
				}
			});
		}
	}

	/**
	 * Check whether the given name points back to(指向) the given alias as an alias
	 * in the other direction already, catching a circular(循环) reference upfront
	 * and throwing a corresponding IllegalStateException.
	 * @param name the candidate(候选) name
	 * @param alias the candidate alias
	 * @see #registerAlias
	 * @see #hasAlias
	 */
	protected void checkForAliasCircle(String name, String alias) {
		if (hasAlias(alias, name)) {
			throw new IllegalStateException("Cannot register alias '" + alias +
					"' for name '" + name + "': Circular reference - '" +
					name + "' is a direct or indirect alias for '" + alias + "' already");
		}
	}

	/**
	 * Determine the raw(原始) name, resolving aliases to canonical(标准) names.
	 * @param name the user-specified name
	 * @return the transformed name
	 * 根据给定的别名获取规范名称
	 */
	public String canonicalName(String name) {
		String canonicalName = name;
		// Handle aliasing...
		String resolvedName;
		do {
			resolvedName = this.aliasMap.get(canonicalName);
			if (resolvedName != null) {
				canonicalName = resolvedName;
			}
		}
		while (resolvedName != null);
		return canonicalName;
	}

}
